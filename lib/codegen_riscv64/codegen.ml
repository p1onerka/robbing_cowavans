open Parser.Types
open Helpers.Bind
open Live_intervals

let codegen program defs_list main_ident =
  let Ident (main_id, main_pos) = main_ident in
  let output_file = open_out (Filename.concat "./out" "output.S") in
  let var_info_handler var_info vars =
    match var_info with | None -> vars| Some v ->
      (VarHeap.add (VarHeap.delete_one varheap_eq v vars) v)
  in
  let find_var_s_placement ident pos live_intervals context =
    match VarHeap.find varheap_eq (ident, Reg "fake reg") context.vars with
    | Some v -> let (_, placement) = v in placement, live_intervals, context, false
    | None -> let allocated_reg, live_intervals, context =
      initially_to_reg_alloc [] pos live_intervals context output_file
      in Reg allocated_reg, live_intervals, context, true
  in

  (*could be shorten for demo; default a0-a7 @ t0-t6*) (* a* regs should be first *)
  let init_free_regs = FStack.add_list FStack.create ["a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
  "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"] in
  let* init_live_intervals_heaps, init_live_intervals_heaps_count, init_calls_list = 
    let* lih, calls_list = compose_live_intervals_heaps_and_calls_list program  defs_list in
      match lih with
    | [] -> `Success([], 0, calls_list)
    | _ -> `Success (lih, (List.length lih), calls_list)
  in

  let init_active = IntervalMinFinishHeap.empty in

  (* forms assembly code for arithm expr *)
  (* sug_reg (suggested reg) = None | Some (register, fa_flag): fa_flag = first assing flag.
  If not fa_flag then you can't move first opernad to register cause var from left part of
  assignment could be part of second operand *)
  (* anon_employed: registers that employed by missing in active something*) 
    let rec codegen_expr ?(sug_reg = None) pos expr untouchables anon_employed context calls_list =
      match expr with
      (* expr is single const => just load it into first enable register (default a0) *)
      | Const x -> (match sug_reg with
        | Some (r, _) ->
          (Printf.fprintf output_file "li %s, %s\n" r x; (*load number 'x' into reg 'r' *)
          (*true for repl_flag (replaceable flag)*)
          (* None / Some of ident * var_s_placement: after calc second operand: if Some x: have to add x to
            vars instead of current with this id*)
          (r, context), calls_list, None, true)
        | None ->
          (let register, context = 
            get_free_reg untouchables pos context output_file
          in
            Printf.fprintf output_file "li %s, %s\n" register x; (*load number 'x' into reg 'register' *)
            (register, context), calls_list, None, true))

      (* expr is var => search for it in stack/registers *)
      | Var Ident (id, pos) -> (*snd is Reg "fake reg" cause it is unused in varheap_eq*) 
        (let (_, placement) as var_info = 
          match VarHeap.find varheap_eq (Ident (id, pos), Reg "fake reg") context.vars with
          | None -> failwith "file codegen.ml/fun codegen_expr" (*unreachable*)
          | Some v -> v
          in match placement with
            | Reg r ->
              (r, context),calls_list, None, false
            | OnStack (offset, interval) ->
              let reg = Option.bind sug_reg (fun a -> Some (fst a)) in
                move_spilled_var_to_reg untouchables pos ~reg:reg offset interval context output_file, 
                calls_list,
                Some var_info,
                true)
      (* expr is binop => codegen each *)
      | Binop (op, e1, e2) -> 
        (let com = (match op with
          | Plus -> "add"
          | Minus -> "sub";
          | Multiply -> "mul"
          | Divide -> "div")
        in
        let sug_reg1 = match sug_reg with | Some (_, fa_flag) when fa_flag -> sug_reg | _ -> None in
          let (r1, context), calls_list, var_info1, repl_flag1 = 
            codegen_expr pos e1 untouchables anon_employed context calls_list ~sug_reg:sug_reg1
          in (*case1: e1 res has not loaded to 'reg', case2: has loaded or sug_reg is None *)
            let sug_reg2 = match r1, sug_reg with
              | r, Some (register, _) when r <> register -> sug_reg
              | _ -> None
            in 
            let untouchables, anon_employed = if repl_flag1 then untouchables, r1::anon_employed else match e1 with
              | Var Ident (id, _) -> id :: untouchables, anon_employed
              | _ -> failwith "file codegen.ml / fun codegen_expr / 1" (*unreachable*)
            in
              let (r2, context),calls_list, var_info2, repl_flag2 =
                codegen_expr pos e2 untouchables anon_employed context calls_list ~sug_reg:sug_reg2
              in
                let vars = var_info_handler var_info1 context.vars in
                  let context = {context with  vars = var_info_handler var_info2 vars} in 
                    let (res_reg, context), final = 
                      match (repl_flag1, repl_flag2, sug_reg) with
                        | false, false, None -> 
                          (let unt = if repl_flag2 && r2<>r1 then untouchables else match e2 with
                              |Var Ident (id, _) -> id :: untouchables
                              | _ -> failwith "file codegen.ml / fun codegen_expr / 2" (*unreachable*)
                          in
                            (get_free_reg unt pos context output_file),
                            (fun _ _ fr -> fr))
                        | false, false, Some (r,_) ->
                          (r, context), (fun _ _ fr -> fr)
                        | false, true, None -> 
                          (r2, context), (fun _ _ fr -> fr) 
                        | true, true, None -> 
                          (r1, context), (fun _ r2 fr -> FStack.push r2 fr)
                        | _, true, Some (r, _) -> if r1 = r then
                            (r, context), (fun _ r2 fr -> FStack.push r2 fr)
                          else (r2, context), (fun _ _ fr -> fr)
                        | _, _, None -> (r1, context), (fun _ _ fr -> fr)
                        | _, _, Some (r, _) -> if r = r2 then 
                            (r, context), (fun r1 _ fr -> FStack.push r1 fr)
                          else (r1, context), (fun _ _ fr -> fr)
                        in
                    (Printf.fprintf output_file "%s %s, %s, %s\n" com res_reg r1 r2; (*make binop, store res to reg 'res_reg'*)
                    let free_regs = final r1 r2 context.free_regs in 
                      (res_reg, {context with free_regs = free_regs}), calls_list, None, true))
                | Func_Call ( _, args) -> (match calls_list with
                  | [] -> failwith "file codegen.ml / fun codegen expr / 3" (*unreachable*)
                  | hd::tl -> (let Ident (def_id, def_pos) = hd in
                    let context1, calls_list = prepare_function_call pos args {context with protected = []} tl ~anon_employed:anon_employed in
                      Printf.fprintf output_file "call %s%d\n" def_id def_pos;
                      let register, context = match sug_reg with
                        | Some (register, _) -> register, context
                        | None -> get_free_reg untouchables pos context output_file
                      in
                        Printf.fprintf output_file "mv %s, a0\n" register;
                        List.iter (fun (r, offset, _) -> if r <> register
                          then Printf.fprintf output_file "ld %s, %d(s0)\n" r offset ) context1.protected;
                        (register, context), calls_list, None, true)
                         )
    (* calls codegen for expr func, then 
      if var is already declared, generates code for placing new value in its address, 
      if not, places it in reg/stack (additionaly grows it). then calls statements codegen *)
      and codegen_assignment_and_tail assign tail live_intervals live_intervals_heaps context calls_list =
        let (Ident (id, pos), expr) =  assign in
            let var_placement, live_intervals, context, fa_flag =
              find_var_s_placement (Ident (id, pos)) pos live_intervals context
            in
              match var_placement with
              | OnStack (offset, _) -> 
                (let (register, context), calls_list, var_info, repl_flag =
                  codegen_expr pos expr [] [] context calls_list
                in
                  let vars = var_info_handler var_info context.vars in
                    Printf.fprintf output_file "sd %s, %d(s0)\n" register offset;  (*load expr res to (on stack) var placement*)
                    let free_regs = if not repl_flag then context.free_regs else FStack.push register context.free_regs in 
                       codegen_statements tail live_intervals live_intervals_heaps calls_list {context with free_regs = free_regs; vars = vars})
              | Reg r ->
                let (register, context),calls_list, var_info, repl_flag =
                  codegen_expr pos expr (id::[]) [] context calls_list ~sug_reg:(Some (r, fa_flag))
                  in
                    let vars = var_info_handler var_info context.vars in
                      if register <> r then
                        (Printf.fprintf output_file "mv %s, %s\n" r register; (*move expr res from reg 'register' to reg 'r'*)
                        let free_regs = if not repl_flag then context.free_regs else FStack.push register context.free_regs in
                          codegen_statements tail live_intervals live_intervals_heaps calls_list {context with vars = vars; free_regs = free_regs})
                      else codegen_statements tail live_intervals live_intervals_heaps calls_list context

      and codegen_wdd_and_tail ((comp, st, pos), tail) live_intervals live_intervals_heaps context calls_list =
        (* labels contain position of start of the loop, so they are unique for each loop *)
        let start_label = Printf.sprintf ".while_%d_lbl" pos in
        let end_label = Printf.sprintf ".done_%d_lbl" pos in
          Printf.fprintf output_file "%s:\n" start_label;
            let context1, calls_list =
            (* depth + 1 for while !!! cause always calc comporision before quit*)
              codegen_branching pos comp end_label {context with depth = context.depth + 1} calls_list
            in
            let sort_n_hd_additions n acc list =
              let rec sort n acc list1 list =
                if n = 0 then acc, list1 else
                  match list with
                  | [] -> failwith "n should be less then list's lenth"
                  | hd::tl -> let (_, _, depth_dif) = hd in if depth_dif = -1 then sort (n-1) (hd::acc) list1 tl
                    else  sort (n-1) acc (hd::list1) tl
              in sort n acc list list
            in
              let protected_additions, protected = 
                sort_n_hd_additions (List.length context1.protected - List.length context.protected) [] context1.protected
              in
                let context = { context1 with protected = protected; depth = context.depth} in
                  let live_intervals, live_intervals_heaps, stack_memory_info1, calls_list =
                    codegen_statements st live_intervals live_intervals_heaps calls_list {context1 with protected = protected_additions}
                  in
                    if (snd stack_memory_info1) <> (snd context.stack_memory_info)
                      then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd context.stack_memory_info));
                    Printf.fprintf output_file "j %s\n%s:\n" start_label end_label;
                    codegen_statements tail live_intervals live_intervals_heaps calls_list context

      and codgen_itef_and_tail itef tail live_intervals live_intervals_heaps context calls_list =
        let comp, (then_branch, _), (else_branch, _), pos = itef in
        let start_label = Printf.sprintf ".if_%d_lbl" pos in 
        let else_label = Printf.sprintf ".else_%d_lbl" pos in
        let fi_label = Printf.sprintf ".fi_%d_lbl" pos in
        Printf.fprintf output_file "%s:\n" start_label;
            let context, calls_list =
              codegen_branching pos comp else_label context calls_list
            in
              let live_intervals, live_intervals_heaps, stack_memory_info1, calls_list  =
                codegen_statements then_branch live_intervals live_intervals_heaps calls_list {context with protected = []; depth = context.depth + 1}
              in
                if (snd stack_memory_info1) <> (snd context.stack_memory_info)
                  then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd context.stack_memory_info));
                Printf.fprintf output_file "j %s\n%s:\n" fi_label else_label;
                let live_intervals, live_intervals_heaps,stack_memory_info2, calls_list =
                  codegen_statements else_branch live_intervals live_intervals_heaps calls_list {context with protected = []; depth = context.depth + 1}
                in
                  if (snd stack_memory_info2) <> (snd context.stack_memory_info)
                  then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd context.stack_memory_info));
                  Printf.fprintf output_file "%s:\n" fi_label;
                  codegen_statements tail live_intervals live_intervals_heaps calls_list context

      and codegen_branching pos comparision else_branch_label context calls_list =
        let Comparision (comp_op, expr1, expr2) = comparision in
          let branching_op =
            match comp_op with
            | Not_equal -> "beq"
            | Equal -> "bne"
            | Less_or_equal -> "bgt"
            | Less -> "bge"
            | Greater_or_equal -> "blt"
            | Greater -> "ble"
          in
            let (register1, context), calls_list,  var_info, repl_flag1 = 
              codegen_expr pos expr1 [] [] context calls_list
            in
              let vars = var_info_handler var_info context.vars in
                let untouchables = match repl_flag1, expr1 with | false,  Var Ident (id, _) -> id::[] | _ -> [] in
                  let (register2, context), calls_list, var_info, repl_flag2 =
                    codegen_expr pos expr2 untouchables [] {context with vars = vars} calls_list
                  in
                    let vars = var_info_handler var_info context.vars in
                      Printf.fprintf output_file "%s %s, %s, %s\n" branching_op register1 register2 else_branch_label;
                        let free_regs = match repl_flag1, repl_flag2 with
                          | true, false -> FStack.push register1 context.free_regs
                          | false, true -> FStack.push register2 context.free_regs
                          | true, true -> FStack.push register2 (FStack.push register1 context.free_regs)
                          | _ -> context.free_regs
                        in   
                          {context with vars = vars; free_regs = free_regs}, calls_list
                  
      and codegen_func_def ident params body live_intervals live_intervals_heaps calls_list =
        let take_params params =
          let vars = VarHeap.empty in
          let free_regs = init_free_regs in
          let active = IntervalMinFinishHeap.empty in
          let rec take_stack_params params vars free_regs active live_intervals offset = 
            match params with
            | [] -> vars, free_regs, active, live_intervals
            | hd::tl -> (let live_intervals, interval = match IntervalMinStartHeap.take live_intervals with
              |Some (live_intervals, interval) -> live_intervals, interval
              |None  -> failwith "file codegen.ml / fun codegen_func_def" (*unreachable*)
              in match (FStack.pop free_regs) with
                | None -> take_stack_params tl (VarHeap.add vars (hd, OnStack (offset, interval))) free_regs
                  (IntervalMinFinishHeap.add active interval) live_intervals (offset + 8)
                | Some (free_regs, r) ->
                  (*move param from stack to reg 'r'*)
                  (Printf.fprintf output_file "ld %s, %d(s0)\n" r offset); (* to implement calle saved registers routine after implementing s regs!!! *)
                  take_stack_params tl (VarHeap.add vars (hd, Reg r)) free_regs 
                    (IntervalMinFinishHeap.add active interval) live_intervals (offset + 8))
          in
            let rec take_params_inner params vars free_regs active live_intervals =
              match params with
              | [] ->  vars, free_regs, active, live_intervals
              | hd::tl ->
                (match (FStack.pop free_regs) with
                | None -> take_stack_params params vars free_regs active live_intervals 0
                | Some (free_regs, r) -> (if r.[0] = 'a' then
                    let live_intervals, interval = match IntervalMinStartHeap.take live_intervals with
                      |Some (live_intervals, interval) -> live_intervals, interval
                      |None  -> failwith "file codegen.ml / fun codegen_func_def" (*unreachable*)
                    in
                      take_params_inner tl (VarHeap.add vars (hd, Reg r )) free_regs (IntervalMinFinishHeap.add active interval) live_intervals
                  else take_stack_params params vars free_regs active live_intervals 0))
            in
              take_params_inner params vars free_regs active live_intervals
        in

          let Ident (id, pos) = ident in
          if List.length live_intervals_heaps <> init_live_intervals_heaps_count - 1 then 
            Printf.fprintf output_file "j %s%d_end\n" id pos;
          Printf.fprintf output_file "\n%s%d:\n" id pos;
          let stack_memory_allocated = 16 in (*must be divisible by 16*)
            Printf.fprintf output_file "addi sp, sp, %d\n" (-stack_memory_allocated);
            Printf.fprintf output_file "sd ra, 8(sp)\nsd s0, 0(sp)\naddi s0, sp, 16\n";
          let vars, free_regs, active, live_intervals = take_params params in
            let context = {
              active = active;
              vars = vars;
              free_regs = free_regs;
              depth = 0;
              protected = []; (* will be changed after implenetating s regs  *)
              stack_memory_info = (16,stack_memory_allocated)
              } 
            in
              let _, live_intervals_heaps, _, calls_list =
                codegen_statements body live_intervals live_intervals_heaps calls_list context
              in 
              Printf.fprintf output_file "\n%s%d_end:\n" id pos;
              live_intervals_heaps, calls_list

      and prepare_function_call ?(anon_employed = []) pos args context calls_list = (*в случае присваивания / expr сюда кидать  позицию присваивания*)
        let context = expire_old_intervals pos context output_file in
        let put_stack_args args context anon_employed calls_list =
          let active_count = IntervalMinFinishHeap.size context.active in
          let args_count = List.length args in
            let context = let rec spill context count = if count = 0 then context else 
              spill (snd (spill_allocated context output_file)) (count - 1) in spill context active_count
            in
              let shortage = args_count * 8 - (snd context.stack_memory_info - fst context.stack_memory_info) in
               if shortage > 0 then (let increase_size = (shortage / 16 + 1) * 16 in
                (*not to change context here and below cause that's unused below (but it maybe change after implementing new features )*)
                Printf.fprintf output_file "addi sp, sp, %d\n" (-increase_size));
              let rec put args context offset calls_list = 
                match args with | [] -> context, calls_list
                | hd::tl -> 
                  let (register, context), calls_list, var_info, repl_flag = codegen_expr pos hd [] anon_employed context calls_list
                  in
                    let vars = var_info_handler var_info context.vars in
                      Printf.fprintf output_file "sd %s %d(sp)\n" register offset;
                      let free_regs = if not repl_flag then context.free_regs else (FStack.push register context.free_regs) in
                         put tl {context with vars = vars; free_regs = free_regs} (offset + 8) calls_list
                    in
                      put args context 0 calls_list
        in
          let rec put_args args after_call_free_regs context anon_employed calls_list =
            match args with |[] -> put_stack_args args context anon_employed calls_list | hd::tl -> (
              match FStack.pop after_call_free_regs with
              | Some (after_call_free_regs, r) when r.[0] = 'a' ->
                let context = get_due_reg r context output_file in
                  let (register, context), calls_list, var_info, repl_flag =
                    codegen_expr pos hd [] anon_employed context calls_list ~sug_reg:(Some(r,true))
                  in
                    let vars = var_info_handler var_info context.vars in
                    let free_regs = if register <> r then
                      Printf.fprintf output_file "mv %s, %s\n" r register;
                      if not repl_flag then context.free_regs
                      else (FStack.push register context.free_regs)
                    in
                      put_args tl after_call_free_regs {context with vars = vars; free_regs = free_regs} (r::anon_employed) calls_list
              | _ -> put_stack_args args context anon_employed calls_list
          )
          in
            let stack_memory_info, protected, free_regs = 
              let rec spill stack_memory_info protected free_regs anon_employed =
                match anon_employed with
                | [] -> stack_memory_info, protected, free_regs
                |hd::tl ->
                  let stack_memory_info = stack_memory_check stack_memory_info output_file in
                    let offset = - (fst stack_memory_info + 8) in
                      Printf.fprintf output_file "ld %s, %d(s0)\n" hd offset;
                      spill (fst stack_memory_info + 8, snd stack_memory_info) ((hd, offset, -1)::protected) (FStack.push hd free_regs) tl
              in
                spill context.stack_memory_info context.protected context.free_regs anon_employed
            in
              put_args args init_free_regs {context with depth = context.depth + 1; stack_memory_info = stack_memory_info;
                protected = protected; free_regs = free_regs} [] calls_list

      (* defines type of first statement in list and calls corresponding codegen func *)
      and codegen_statements  statements live_intervals0 live_intervals_heaps0 calls_list context =
        match statements with
        | Assignment_and_tail (assignment, tail) ->
          codegen_assignment_and_tail assignment tail live_intervals0 live_intervals_heaps0 context calls_list
        | While_Do_Done_and_tail ((comp, (st, _), pos), tail) ->
          codegen_wdd_and_tail ((comp, st, pos), tail) live_intervals0 live_intervals_heaps0 context calls_list
        | Nothing ->
          (if context.depth <> 0 then
           List.iter (fun (r, offset, _) -> Printf.fprintf output_file "ld %s, %d(s0)\n" r offset) context.protected
          else 
            (Printf.fprintf output_file "mv a0, zero\n";
            Printf.fprintf output_file "ld ra, -8(s0)\nld s0, -16(s0)\n";
            Printf.fprintf output_file "jr ra\n"); (*return from func*)
            live_intervals0, live_intervals_heaps0, context.stack_memory_info, calls_list)
        | If_Then_Else_Fi_and_tail (itef, tail) ->
          codgen_itef_and_tail itef tail live_intervals0 live_intervals_heaps0 context calls_list
        | Function_and_tail ((ident, params, (body, _)), tl) ->
          let live_intervals, live_intervals_heaps = match live_intervals_heaps0 with
            | [] -> failwith "file codegen.ml / fun codegen statements / 1" (*unreachable*)
            | hd::tl -> hd,tl
          in
            let live_intervals_heaps, calls_list =
              codegen_func_def ident params body live_intervals live_intervals_heaps calls_list
            in codegen_statements tl live_intervals live_intervals_heaps calls_list context
        | Function_Call ((Ident (_, pos), args), tail) ->
          (match calls_list with
          | [] -> failwith "file codegen.ml / fun codegen statements / 1" (*unreachable*)
          | hd::tl -> (let Ident (def_id, def_pos) = hd in
            let context1, calls_list =
              prepare_function_call pos args {context with protected = []} tl 
            in
              Printf.fprintf output_file "call %s%d\n" def_id def_pos;
              List.iter (fun (r, offset, _) -> Printf.fprintf output_file "ld %s, %d(s0)\n" r offset ) context1.protected;
              codegen_statements tail live_intervals0 live_intervals_heaps0 calls_list context))
        | Return (expr, tail) -> 
          (let (register, _), calls_list, _, _ =
            codegen_expr (-1) expr [] [] context ~sug_reg:(Some("a0",true)) calls_list
          in
            if register <> "a0" then
              Printf.fprintf output_file "mv a0, %s\n" register;
            Printf.fprintf output_file "ld ra, -8(s0)\nld s0, -16(s0)\n";
            Printf.fprintf output_file "jr ra\n"; (*return from func*)
            codegen_statements tail live_intervals0 live_intervals_heaps0 calls_list context)
      in
          Printf.fprintf output_file ".global _start\n\n_start:\n";
          Printf.fprintf output_file "call %s%d\n" main_id main_pos;
          Printf.fprintf output_file "li a0, 0\nli a7, 93\necall\n";
            let init_context = {
              vars = VarHeap.empty;
              active = init_active;
              free_regs = init_free_regs;
              protected = [];
              depth = 0;
              stack_memory_info = (0, 0)
            } in
              let _,_,_,_ =
                codegen_statements program IntervalMinStartHeap.empty init_live_intervals_heaps init_calls_list init_context
              in `Success ""