open Parser.Types
open Helpers.Bind
let codegen program =
  let output_file = open_out (Filename.concat "./out" "output.S") in
  let regs = ["a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7"; "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"] in
    let regs_len = List.length regs in
  let print_var var =
  let id, offset = var in
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
      Printf.fprintf output_file
      (*load value and call print_int*)
        "addi sp, sp, -8\nld a0, %d(s0)\nsd ra, 8(sp)\ncall print_int\n\
        ld ra, 8(sp)\naddi sp, sp, 8\n" offset
  in
  (* forms assembly code for arithm expr *)
  let rec codegen_expr ?(reg = 0) expr vars =
    match expr with
    (* expr is var => search for it in stack *)
    | Var Ident (id, pos) ->
      (match List.find_opt (fun var -> String.equal id (fst var)) vars with
      | Some var  -> 
        Printf.fprintf output_file "ld %s, %d(s0)\n" (List.nth regs reg) (snd var);
        `Success ""
      | None ->  `Error ("can't find variable '" ^ id ^ "' definition", pos))
    (* expr is single const => just load it into first enable register (default a0) *)
    | Const x -> Printf.fprintf output_file "li %s, %s\n" (List.nth regs reg) x; `Success ""
    (* expr is binop => codegen each *)
    | Binop (op, e1, e2) ->
      if (reg + 1) >= regs_len then failwith "too much nested expressions" 
      else
        (let* _ = codegen_expr ~reg:(reg) e1 vars in ();
        let* _ = codegen_expr ~reg:(reg + 1) e2 vars in ();
        let reg1 = (List.nth regs reg) in
          let reg2 = (List.nth regs (reg + 1)) in
            let print_ariphm_comand com =
              Printf.fprintf output_file "%s %s, %s, %s\n" com reg1 reg1 reg2 in
                print_ariphm_comand (match op with
                  | Plus -> "add"
                  | Minus -> "sub";
                  | Multiply -> "mul"
                  | Divide -> "div");
                `Success "")
  in
  (* calls codegen for expr func, then 
     if var is already declared, generates code for placing new value in its address, 
     if not, places it in stack (additionaly grows it). then calls statements codegen *)
  let rec codegen_assignment_and_tail assign tail vars stack_memory_allocated is_main_thr =
    let (Ident (id, _), expr) =  assign in
      let* _ = codegen_expr expr vars in ();
      match List.find_opt (fun var -> String.equal id (fst var)) vars with
      | Some var ->  
        Printf.fprintf output_file "sd a0, %d(s0)\n" (snd var);
         codegen_statements  tail vars stack_memory_allocated
      | None -> 
        let offest =  match vars with
          | [] -> -8 
          | not_empty_list ->
            (snd (List.nth  not_empty_list 0) - 8)
        in
        let stack_memory_allocated =
          match stack_memory_allocated < -offest with
          (* grows stack downwards for 24 bytes, takes 8 for newmade var *)
          |true -> let stack_memory_gain = 24 in
            Printf.fprintf output_file "addi sp, sp, -%d\n" stack_memory_gain;
            stack_memory_allocated + 24;
          |false -> stack_memory_allocated
        in
        let vars = (id, offest) :: vars in
        Printf.fprintf output_file "sd a0, %d(s0)\n" offest;
        codegen_statements ~is_main_thr:is_main_thr tail vars stack_memory_allocated

  and codegen_wdd_and_tail ((comp, st, pos), tail) vars stack_memory_allocated is_main_thr =
    (* labels contain position of start of the loop, so they are unique for each loop *)
    let start_label = Printf.sprintf ".while_%d_lbl" pos in
    let end_label = Printf.sprintf ".done_%d_lbl" pos in
      Printf.fprintf output_file "%s:\n" start_label;
      let* _ = codegen_branching comp vars end_label in ();
      let* _ = codegen_statements st vars stack_memory_allocated in ();
        Printf.fprintf output_file "addi sp, s0, -%d\n" stack_memory_allocated; 
        Printf.fprintf output_file "j %s\n%s:\n" start_label end_label;
        codegen_statements ~is_main_thr:is_main_thr tail vars stack_memory_allocated

  and codgen_itef_and_tail itef tail vars stack_memory_allocated is_main_thr =
    let comp, then_branch, else_branch, pos = itef in
    let start_label = Printf.sprintf ".if_%d_lbl" pos in 
    let else_label = Printf.sprintf ".else_%d_lbl" pos in
    let fi_label = Printf.sprintf ".fi_%d_lbl" pos in
      Printf.fprintf output_file "%s:\n" start_label;
      let* _ = codegen_branching comp vars else_label in ();
      let* _ = codegen_statements then_branch vars stack_memory_allocated in ();
      Printf.fprintf output_file "addi sp, s0, -%d\n" stack_memory_allocated;
      Printf.fprintf output_file "j %s\n%s:\n" fi_label else_label;
      let* _ = codegen_statements else_branch vars stack_memory_allocated in ();
      Printf.fprintf output_file "addi sp, s0, -%d\n" stack_memory_allocated; 
      Printf.fprintf output_file "%s:\n" fi_label;
      codegen_statements ~is_main_thr:is_main_thr tail vars stack_memory_allocated

  and codegen_branching comparision vars else_branch_label =
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
    let* _ = codegen_expr expr1 vars in ();
    let* _ = codegen_expr ~reg:1 expr2 vars in ();
    (Printf.fprintf output_file "%s a0, a1, %s\n" branching_op else_branch_label;
    `Success "")
  (* defines type of first statement in list and calls corresponding codegen func *)
  and codegen_statements ?(is_main_thr = false) statements vars stack_memory_allocated =
    match statements with
    | Assignment_and_tail (assignment, tail) ->
      codegen_assignment_and_tail assignment tail vars stack_memory_allocated is_main_thr;
    | While_Do_Done_and_tail ((comp, st, pos), tail) ->
      codegen_wdd_and_tail ((comp, st, pos), tail) vars stack_memory_allocated  is_main_thr;
    | Nothing -> if is_main_thr then
      (Printf.fprintf output_file ".print_vars:\n";
      List.iter print_var vars);
      `Success ""
    | If_Then_Else_Fi_and_tail (itef, tail) ->
      codgen_itef_and_tail itef tail vars stack_memory_allocated is_main_thr;
  in
    let stack_memory_allocated = 24 in
      Printf.fprintf output_file ".global _start\n\n_start:\n";
      Printf.fprintf output_file "addi sp, sp, -%d\naddi s0, sp, %d\n" stack_memory_allocated stack_memory_allocated;
      let* _ = codegen_statements ~is_main_thr:true program [] stack_memory_allocated in ();
      Printf.fprintf output_file "li a0, 0\nli a7, 93\necall\n";
      `Success ""
