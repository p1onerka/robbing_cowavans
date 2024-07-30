(*
open Parser.Types
open Helpers.Bind
open Live_intervals

let codegen program =
  let output_file = open_out (Filename.concat "./out" "output.S") in
  let var_info_handler var_info vars  =
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

  (*could be shorten for demo; default a0-a7 @ t0-t6*)
  let init_free_regs = FStack.add_list FStack.create ["a0"; "a1"; "a2"] in
  let*init_live_intervals = compose_live_intervals program in
  let init_active = IntervalMinFinishHeap.empty in

  (* let print_var var =
    let Ident (id, _), placement = var in
      let length = String.length id in
      (*call mmap*)
      Printf.fprintf output_file "li a0, 0\nli a1, %d\nli a2, 3\nli a3, 33\n\
      li a4, -1\nli a5, 0\nli a7, 222\necall\n" (length + 4);
      (* code of \n = 10 *)
      Printf.fprintf output_file "li a1, 10\nsd a1, (a0)\n";
      (* load id *)
      String.iteri ( fun i ch ->
        Printf.fprintf output_file "li a1, %d\nsd a1, %d(a0)\n" (Char.code ch) (i + 1)) id;
        (* space + '=' + space *) (* print *) (*call munmap*)
      Printf.fprintf output_file
        "li a1, 32\nli a2, 61\nsd a1, %d(a0)\nsd a2, %d(a0)\nsd a1, %d(a0)\nmv a1, a0\n\
        li a0, 1\nli a2, %d\nli a7, 64\necall\nmv a0, a1\nli a1, %d\nli a7, 215\necall\n"
         (length + 1) (length + 2) (length + 3) (length + 4) (length + 4);
      match  placement with
      |  Red r -> pattern
      Printf.fprintf output_file (*a вот теперь надо соблюдать call convention, так что тут все active надо сохранять. :/ TODO*)
      (*save ret_adr and call print_int*)
        "addi sp, sp, -8\nsd ra, 8(sp)\ncall print_int\n\
        ld ra, 8(sp)\naddi sp, sp, 8\n" offset *)
  (* in *)



  (* forms assembly code for arithm expr *)
  (* sug_reg (suggested reg) = None | Some (register, fa_flag): fa_flag = first assing flag.
  If not fa_flag then you can't move first opernad to register cause var from left part of
  assignment could be part of second operand *)
    let rec codegen_expr ?(sug_reg = None) pos expr untouchables context =
      match expr with
      (* expr is single const => just load it into first enable register (default a0) *)
      | Const x -> (match sug_reg with
        | Some (r, _) ->
          (Printf.fprintf output_file "li %s, %s\n" r x; (*load number 'x' into reg 'r' *)
          (*true for repl_flag (replaceable flag)*)
          (* None / Some of ident * var_s_placement: after calc second operand: if Some x: have to add x to
            vars instead of current with this id*)
          (r, context), None, true)
        | None ->
          (let register, context = 
            get_free_reg untouchables pos context output_file
          in
            Printf.fprintf output_file "li %s, %s\n" register x; (*load number 'x' into reg 'register' *)
            (register, context), None, true))

      (* expr is var => search for it in stack/registers *)
      | Var Ident (id, pos) -> (*snd is Reg "fake reg" cause it is unused in varheap_eq*) 
        (let (_, placement) as var_info = 
          match VarHeap.find varheap_eq (Ident (id, pos), Reg "fake reg") context.vars with
          | None -> failwith "file codegen.ml/fun codegen_expr" (*unreachable*)
          | Some v -> v
          in match placement with
            | Reg r ->
              (r, context), None, false
            | OnStack (offset, interval) -> 
              let reg = Option.bind sug_reg (fun a -> Some (fst a)) in
                move_spilled_var_to_reg untouchables pos ~reg:reg offset interval context output_file,
                Some var_info, true)
      (* expr is binop => codegen each *)
      | Binop (op, e1, e2) -> 
        (let com = (match op with
          | Plus -> "add"
          | Minus -> "sub";
          | Multiply -> "mul"
          | Divide -> "div")
        in
        let sug_reg1 = match sug_reg with | Some (_, fa_flag) when fa_flag -> sug_reg | _ -> None in
          let (r1, context), var_info1, repl_flag1 = 
            codegen_expr pos e1 untouchables context ~sug_reg:sug_reg1
          in (*case1: e1 res has not loaded to 'reg', case2: has loaded or sug_reg is None *)
            let sug_reg2 = match r1, sug_reg with
              | r, Some (register, _) when r <> register -> sug_reg
              | _ -> None
            in 
            let untouchables = if repl_flag1 then untouchables else match e1 with
              | Var Ident (id, _) -> id :: untouchables 
              | _ -> failwith "file codegen.ml / fun codegen_expr" (*unreachable*)
            in
              let (r2, context), var_info2, repl_flag2 =
                codegen_expr pos e2 untouchables context ~sug_reg:sug_reg2
              in
                let vars = var_info_handler var_info1 context.vars in
                  let context = {context with  vars = var_info_handler var_info2 vars} in 
                    let (res_reg, context), final = 
                      match (repl_flag1, repl_flag2, sug_reg) with
                        | false, false, None -> 
                          (let unt = if not repl_flag2 && r2 <> r1 then r2 :: untouchables else untouchables in 
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
                      (res_reg, {context with free_regs = free_regs}), None, true))
    in
    (* calls codegen for expr func, then 
      if var is already declared, generates code for placing new value in its address, 
      if not, places it in reg/stack (additionaly grows it). then calls statements codegen *)
      let rec codegen_assignment_and_tail assign tail live_intervals context =
        let (Ident (id, pos), expr) =  assign in
            let var_placement, live_intervals, context, fa_flag =
              find_var_s_placement (Ident (id, pos)) pos live_intervals context
            in
              match var_placement with
              | OnStack (offset, _) -> 
                (let (register, context),var_info, repl_flag = 
                  codegen_expr pos expr [] context
                in
                  let vars = var_info_handler var_info context.vars in
                    Printf.fprintf output_file "sd %s, %d(s0)\n" register offset;  (*load expr res to (on stack) var placement*)
                    let free_regs = if not repl_flag then context.free_regs else FStack.push register context.free_regs in 
                       codegen_statements tail live_intervals {context with free_regs = free_regs; vars = vars})  
              | Reg r ->
                let (register, context), var_info, repl_flag = 
                  codegen_expr pos expr (id::[]) context ~sug_reg:(Some (r, fa_flag))
                  in
                    let vars = var_info_handler var_info context.vars in
                      if register <> r then
                        (Printf.fprintf output_file "mv %s, %s\n" r register; (*move expr res from reg 'register' to reg 'r'*)
                        let free_regs = if not repl_flag then context.free_regs else FStack.push register context.free_regs in
                          codegen_statements tail live_intervals {context with vars = vars; free_regs = free_regs})
                      else codegen_statements tail live_intervals context

      and codegen_wdd_and_tail ((comp, st, pos), tail) live_intervals context =
        (* labels contain position of start of the loop, so they are unique for each loop *)
        let start_label = Printf.sprintf ".while_%d_lbl" pos in
        let end_label = Printf.sprintf ".done_%d_lbl" pos in
          Printf.fprintf output_file "%s:\n" start_label;
            let context1 =
            (* depth + 1 for while !!! cause always calc comporision before quit*)
              codegen_branching pos comp end_label {context with depth = context.depth + 1}
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
                  let live_intervals, _, _, _, stack_memory_info1 =
                    codegen_statements st live_intervals {context1 with protected = protected_additions}
                  in
                    if (snd stack_memory_info1) <> (snd context.stack_memory_info)
                      then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd context.stack_memory_info));
                    Printf.fprintf output_file "j %s\n%s:\n" start_label end_label;
                    codegen_statements tail live_intervals context

      and codgen_itef_and_tail itef tail live_intervals context =
        let comp, then_branch, else_branch, pos = itef in
        let start_label = Printf.sprintf ".if_%d_lbl" pos in 
        let else_label = Printf.sprintf ".else_%d_lbl" pos in
        let fi_label = Printf.sprintf ".fi_%d_lbl" pos in
        Printf.fprintf output_file "%s:\n" start_label;
            let context =
              codegen_branching pos comp else_label context
            in
              let live_intervals, _, _, _, stack_memory_info1  =
                codegen_statements then_branch live_intervals {context with protected = []; depth = context.depth + 1}
              in
                if (snd stack_memory_info1) <> (snd context.stack_memory_info)
                  then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd context.stack_memory_info));
                Printf.fprintf output_file "j %s\n%s:\n" fi_label else_label;
                let live_intervals, _, _, _, stack_memory_info2 =
                  codegen_statements else_branch live_intervals {context with protected = []; depth = context.depth + 1}
                in
                  if (snd stack_memory_info2) <> (snd context.stack_memory_info)
                  then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd context.stack_memory_info));
                  Printf.fprintf output_file "%s:\n" fi_label;
                  codegen_statements tail live_intervals context

      and codegen_branching pos comparision else_branch_label context =
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
            let (register1, context), var_info, repl_flag1 = 
              codegen_expr pos expr1 [] context
            in
              let vars = var_info_handler var_info context.vars in
                let untouchables = match repl_flag1, expr1 with | false,  Var Ident (id, _) -> id::[] | _ -> [] in
                  let (register2, context), var_info, repl_flag2 =
                    codegen_expr pos expr2 untouchables {context with vars = vars}
                  in
                    let vars = var_info_handler var_info context.vars in
                      Printf.fprintf output_file "%s %s, %s, %s\n" branching_op register1 register2 else_branch_label;
                        let free_regs = match repl_flag1, repl_flag2 with
                          | true, false -> FStack.push register1 context.free_regs
                          | false, true -> FStack.push register2 context.free_regs
                          | true, true -> FStack.push register2 (FStack.push register1 context.free_regs)
                          | _ -> context.free_regs
                        in   
                          {context with vars = vars; free_regs = free_regs}

      (* defines type of first statement in list and calls corresponding codegen func *)
      and codegen_statements  statements live_intervals context =
        match statements with
        | Assignment_and_tail (assignment, tail) ->
          codegen_assignment_and_tail assignment tail live_intervals context
        | While_Do_Done_and_tail ((comp, st, pos), tail) ->
          codegen_wdd_and_tail ((comp, st, pos), tail) live_intervals context
        | Nothing -> 
          ( List.iter (fun (r, offset, _) -> Printf.fprintf output_file "ld %s, %d(s0)\n" r offset ) context.protected;
          live_intervals, context.vars, context.active, context.free_regs, context.stack_memory_info)
        | If_Then_Else_Fi_and_tail (itef, tail) ->
          codgen_itef_and_tail itef tail live_intervals context
      in
        let stack_memory_allocated = 8 in
          Printf.fprintf output_file ".global _start\n\n_start:\n";
          Printf.fprintf output_file "addi sp, sp, %d\naddi s0, sp, %d\n" (-stack_memory_allocated) stack_memory_allocated;
          let _, _, _, _, _ =
            let init_context = {
              vars = VarHeap.empty;
              active = init_active;
              free_regs = init_free_regs;
              protected = [];
              depth = 0;
              stack_memory_info = (0, stack_memory_allocated)
            } in
              codegen_statements program init_live_intervals init_context
          in
            Printf.fprintf output_file "li a0, 0\nli a7, 93\necall\n"; `Success ""
