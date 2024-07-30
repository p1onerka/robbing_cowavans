open Parser.Types
open Helpers.Bind
open Live_intervals

let codegen program =
  let output_file = open_out (Filename.concat "./out" "output.S") in
  let var_info_handler var_info vars  =
    match var_info with | None -> vars| Some v ->
      (VarHeap.add (VarHeap.delete_one varheap_eq v vars) v)
  in
  let find_var_s_placement ident pos live_intervals active vars free_regs depth  protected stack_memory_info =
    match VarHeap.find varheap_eq (ident, Reg "fake reg") vars with
    | Some v -> let (_, placement) = v in 
      (placement, live_intervals, active, vars, free_regs, protected, stack_memory_info, false)
    | None -> let allocated_reg, live_intervals, active, vars, free_regs, protected,  stack_memory_info =
      initially_to_reg_alloc [] pos live_intervals free_regs active vars protected depth  stack_memory_info output_file
      in (Reg allocated_reg, live_intervals, active, vars, free_regs, protected, stack_memory_info, true)
  in

  (*could be shorten for demo; default a0-a7 @ t0-t6*)
  let free_regs = FStack.add_list FStack.create ["a0"; "a1"; "a2"] in
  let* live_intervals = compose_live_intervals program in
  let active = IntervalMinFinishHeap.empty in

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
  (*stack_memory_info is occupied stack memory size and allocated stack memory size *)
  (*depth = last do/then/else block's (for which this expr is inner) depth*)
  (* sug_reg (suggested reg) = None | Some (register, fa_flag): fa_flag = first assing flag.
  If not fa_flag then you can't move first opernad to register cause var from left part of
  assignment could be part of second operand *)
    let rec codegen_expr ?(sug_reg = None) pos expr vars untouchables active free_regs protected depth stack_memory_info =
      match expr with
      (* expr is single const => just load it into first enable register (default a0) *)
      | Const x -> (match sug_reg with
        | Some (r, _) ->
          (Printf.fprintf output_file "li %s, %s\n" r x; (*load number 'x' into reg 'r' *)
          (*true for repl_flag (replaceable flag)*)
          (* None / Some of ident * var_s_placement: after calc second operand: if Some x: have to add x to
            vars instead of current with this id*)
          (r, active, vars, free_regs, protected, stack_memory_info), None, true)
        | None ->
          (let register, active, vars, free_regs, protected, stack_memory_info = 
            get_free_reg untouchables pos free_regs active vars protected depth stack_memory_info output_file
          in
            Printf.fprintf output_file "li %s, %s\n" register x; (*load number 'x' into reg 'register' *)
            (register, active, vars, free_regs, protected, stack_memory_info), None, true))

      (* expr is var => search for it in stack/registers *)
      | Var Ident (id, pos) -> (*snd is Reg "fake reg" cause it is unused in varheap_eq*) 
        (let (_, placement) as var_info = match VarHeap.find varheap_eq (Ident (id, pos), Reg "fake reg") vars with
        | None -> failwith "file codegen.ml/fun codegen_expr" (*unreachable*)
        | Some v -> v
        in match placement with
          | Reg r ->
            (r, active, vars, free_regs, protected, stack_memory_info), None, false
          | OnStack (offset, interval) -> 
            let reg = Option.bind sug_reg (fun a -> Some (fst a)) in
              (move_spilled_var_to_reg untouchables pos ~reg:reg offset interval active free_regs vars protected depth  stack_memory_info output_file),
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
          let (r1, active, vars, free_regs, protected,  stack_memory_info), var_info1, repl_flag1 = 
            codegen_expr pos e1 vars untouchables active free_regs protected depth  stack_memory_info ~sug_reg:sug_reg1
          in (*case1: e1 res has not loaded to 'reg', case2: has loaded or sug_reg is None *)
            let sug_reg2 = match r1, sug_reg with
              | r, Some (register, _) when r <> register -> sug_reg
              | _ -> None
            in 
            let untouchables = if repl_flag1 then untouchables else match e1 with
              | Var Ident (id, _) -> id :: untouchables 
              | _ -> failwith "file codegen.ml / fun codegen_expr" (*unreachable*)
            in
              let (r2, active, vars, free_regs, protected, stack_memory_info), var_info2, repl_flag2 =
                codegen_expr pos e2 vars untouchables active free_regs protected depth  stack_memory_info ~sug_reg:sug_reg2
              in
                let vars = var_info_handler var_info1 vars in
                  let vars = var_info_handler var_info2 vars in 
                    let (res_reg, active, vars, free_regs, protected, stack_memory_info), final = 
                      match (repl_flag1, repl_flag2, sug_reg) with
                        | false, false, None -> 
                          (let unt = if not repl_flag2 && r2 <> r1 then r2 :: untouchables else untouchables in 
                            (get_free_reg unt pos free_regs active vars protected depth  stack_memory_info output_file),
                            (fun _ _ fr -> fr))
                        | false, false, Some (r,_) ->
                          (r, active, vars, free_regs, protected, stack_memory_info), (fun _ _ fr -> fr)
                        | false, true, None -> 
                          (r2, active, vars, free_regs, protected, stack_memory_info), (fun _ _ fr -> fr) 
                        | true, true, None -> 
                          (r1, active, vars, free_regs, protected, stack_memory_info), (fun _ r2 fr -> FStack.push r2 fr)
                        | _, true, Some (r, _) -> if r1 = r then
                            (r, active, vars, free_regs, protected, stack_memory_info), (fun _ r2 fr -> FStack.push r2 fr)
                          else (r2, active, vars, free_regs, protected, stack_memory_info), (fun _ _ fr -> fr)
                        | _, _, None -> (r1, active, vars, free_regs, protected, stack_memory_info), (fun _ _ fr -> fr)
                        | _, _, Some (r, _) -> if r = r2 then 
                            (r, active, vars, free_regs, protected, stack_memory_info), (fun r1 _ fr -> FStack.push r1 fr)
                          else (r1, active, vars, free_regs, protected, stack_memory_info), (fun _ _ fr -> fr)
                        in
                    (Printf.fprintf output_file "%s %s, %s, %s\n" com res_reg r1 r2; (*make binop, store res to reg 'res_reg'*)
                    let free_regs = final r1 r2 free_regs in 
                      (res_reg, active, vars, free_regs, protected, stack_memory_info), None, true))
    in
    (* calls codegen for expr func, then 
      if var is already declared, generates code for placing new value in its address, 
      if not, places it in reg/stack (additionaly grows it). then calls statements codegen *)
      let rec codegen_assignment_and_tail assign tail live_intervals vars active free_regs protected depth  stack_memory_info =
        let (Ident (id, pos), expr) =  assign in
            let var_placement, live_intervals, active, vars, free_regs, protected, stack_memory_info, fa_flag =
              find_var_s_placement (Ident (id, pos)) pos live_intervals active vars free_regs depth  protected stack_memory_info
            in
              match var_placement with
              | OnStack (offset, _) -> 
                (let (register, active, vars, free_regs, protected, stack_memory_info),var_info, repl_flag = 
                  codegen_expr pos expr vars [] active free_regs protected depth  stack_memory_info
                in
                  let vars = var_info_handler var_info vars in
                    Printf.fprintf output_file "sd %s, %d(s0)\n" register offset;  (*load expr res to (on stack) var placement*)
                    let free_regs = if not repl_flag then free_regs else FStack.push register free_regs in 
                       codegen_statements tail live_intervals vars active free_regs protected depth  stack_memory_info)   
              | Reg r ->
                let (register, active, vars, free_regs, protected, stack_memory_info), var_info, repl_flag = 
                  codegen_expr pos expr vars (id::[]) active free_regs protected depth  stack_memory_info ~sug_reg:(Some (r, fa_flag))
                  in
                    let vars = var_info_handler var_info vars in
                      if register <> r then
                        (Printf.fprintf output_file "mv %s, %s\n" r register; (*move expr res from reg 'register' to reg 'r'*)
                        let free_regs = if not repl_flag then free_regs else FStack.push register free_regs in
                          codegen_statements tail live_intervals vars active free_regs protected depth  stack_memory_info)
                      else codegen_statements tail live_intervals vars active free_regs protected depth  stack_memory_info

      and codegen_wdd_and_tail ((comp, st, pos), tail) vars active free_regs live_intervals protected depth stack_memory_info =
        (* labels contain position of start of the loop, so they are unique for each loop *)
        let start_label = Printf.sprintf ".while_%d_lbl" pos in
        let end_label = Printf.sprintf ".done_%d_lbl" pos in
          Printf.fprintf output_file "%s:\n" start_label;
            let vars, active, free_regs, protected1, stack_memory_info =
            (* depth + 1 for while !!! cause always calc comporision before quit*)
              codegen_branching pos comp end_label vars active free_regs protected (depth + 1)  stack_memory_info
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
              let (protected_additions, protected) = sort_n_hd_additions (List.length protected1 - List.length protected) [] protected1 in
                let live_intervals, _, _, _, stack_memory_info1 =
                  codegen_statements st live_intervals vars active free_regs protected_additions (depth + 1) stack_memory_info
                in
                  if (snd stack_memory_info1) <> (snd stack_memory_info)
                    then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd stack_memory_info));
                  Printf.fprintf output_file "j %s\n%s:\n" start_label end_label;
                  codegen_statements  tail live_intervals vars active free_regs protected depth  stack_memory_info

      and codgen_itef_and_tail itef tail vars active free_regs live_intervals protected depth  stack_memory_info =
        let comp, then_branch, else_branch, pos = itef in
        let start_label = Printf.sprintf ".if_%d_lbl" pos in 
        let else_label = Printf.sprintf ".else_%d_lbl" pos in
        let fi_label = Printf.sprintf ".fi_%d_lbl" pos in
        Printf.fprintf output_file "%s:\n" start_label;
            let vars, active, free_regs, protected, stack_memory_info =
              codegen_branching pos comp else_label vars active free_regs protected depth  stack_memory_info
            in
              let live_intervals, _, _, _, stack_memory_info1  =
                codegen_statements then_branch live_intervals vars active free_regs [] (depth + 1)  stack_memory_info
              in
                if (snd stack_memory_info1) <> (snd stack_memory_info)
                  then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd stack_memory_info));
                Printf.fprintf output_file "j %s\n%s:\n" fi_label else_label;
                let live_intervals, _, _, _, stack_memory_info2 =
                  codegen_statements else_branch live_intervals vars active free_regs [] (depth + 1)  stack_memory_info
                in
                if (snd stack_memory_info2) <> (snd stack_memory_info)
                  then Printf.fprintf output_file "addi sp, s0, %d\n"(-(snd stack_memory_info));
                Printf.fprintf output_file "%s:\n" fi_label;
                codegen_statements tail live_intervals vars active free_regs protected depth  stack_memory_info

      and codegen_branching pos comparision else_branch_label vars active free_regs protected depth  stack_memory_info =
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
            let (register1, active, vars, free_regs, protected, stack_memory_info), var_info, repl_flag1 = 
              codegen_expr pos expr1 vars [] active free_regs protected depth  stack_memory_info
            in
              let vars = var_info_handler var_info vars in
                let untouchables = match repl_flag1, expr1 with | false,  Var Ident (id, _) -> id::[] | _ -> [] in
                  let (register2, active, vars, free_regs, protected, stack_memory_info), var_info, repl_flag2 =
                    codegen_expr pos expr2 vars untouchables active free_regs protected depth  stack_memory_info
                  in
                    let vars = var_info_handler var_info vars in
                      Printf.fprintf output_file "%s %s, %s, %s\n" branching_op register1 register2 else_branch_label;
                        let free_regs = match repl_flag1, repl_flag2 with
                          | true, false -> FStack.push register1 free_regs
                          | false, true -> FStack.push register2 free_regs
                          | true, true -> FStack.push register2 (FStack.push register1 free_regs)
                          | _ -> free_regs
                        in   
                          (vars, active, free_regs, protected, stack_memory_info)

      (* defines type of first statement in list and calls corresponding codegen func *)
      and codegen_statements  statements live_intervals vars active free_regs protected depth  stack_memory_info =
        match statements with
        | Assignment_and_tail (assignment, tail) ->
          codegen_assignment_and_tail assignment tail live_intervals vars active free_regs protected depth  stack_memory_info
        | While_Do_Done_and_tail ((comp, st, pos), tail) ->
          codegen_wdd_and_tail ((comp, st, pos), tail) vars active free_regs live_intervals protected depth  stack_memory_info
        | Nothing -> 
          ( List.iter (fun (r, offset, _) -> Printf.fprintf output_file "ld %s, %d(s0)\n" r offset ) protected;
          (live_intervals, vars, active, free_regs, stack_memory_info))
        | If_Then_Else_Fi_and_tail (itef, tail) ->
          codgen_itef_and_tail itef tail vars active free_regs live_intervals protected depth  stack_memory_info 
      in
        let stack_memory_allocated = 8 in
          Printf.fprintf output_file ".global _start\n\n_start:\n";
          Printf.fprintf output_file "addi sp, sp, %d\naddi s0, sp, %d\n" (-stack_memory_allocated) stack_memory_allocated;
          (* print_intervalsHeap_sorted live_intervals; *) (*<-debug*)
          let _, _, _, _, _ = 
            codegen_statements program live_intervals VarHeap.empty active free_regs [] 0 (0, stack_memory_allocated)
          in
            Printf.fprintf output_file "li a0, 0\nli a7, 93\necall\n"; `Success ""