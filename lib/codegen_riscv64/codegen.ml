open Parser.Types

let codegen program =
  let regs = ["a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
 "a8"; "t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"] in
  let regs_len = List.length regs in
  (* forms assembly code for arithm expr *)
  let rec codegen_expr ?(reg = 0) expr vars =
    match expr with
    (* expr is single const => just load it into first enable register (default a0) *)
    | Const x -> Printf.printf "li %s, %d\n" (List.nth regs reg) x
    (* expr is var => search for it in stack *)
    | Var Ident id ->
      (match List.find_opt (fun var -> String.equal id (fst var)) vars with
      | Some var  -> Printf.printf "ld %s, %d(s0)\n" (List.nth regs reg) (snd var)
      | None -> failwith ("can't find variable '" ^ id ^ "' definition"))
    (* expr is binop => codegen each *)
    | Binop (op, e1, e2) -> 
      if (reg + 1) >= regs_len then failwith "too much nested expressions" else
        codegen_expr ~reg:(reg) e1 vars;
        codegen_expr ~reg:(reg + 1) e2 vars;
        let reg1 = (List.nth regs reg)
        in
        let reg2 = (List.nth regs (reg + 1))
        in
        let print_ariphm_comand com =
          Printf.printf "%s %s, %s, %s\n" com reg1 reg1 reg2
      in
      print_ariphm_comand
        (match op with
        | Plus -> "add"
        | Minus -> "sub";
        | Multiply -> "mul";
        | Divide -> "div")
  in

  (* calls codegen for expr func, then 
     if var is already declared, generates code for placing new value in its address, 
     if not, places it in stack (additionaly grows it). then calls statements codegen *)
  let rec codegen_assignment_and_tail assign tail vars stack_memory_allocated =
    let (Ident id, expr) =  assign in
      codegen_expr expr vars;
      match List.find_opt (fun var -> String.equal id (fst var)) vars with
      | Some var ->  
        Printf.printf "sd a0, %d(s0)\n" (snd var);
         codegen_statements  tail vars stack_memory_allocated
      | None -> 
        let offest =  match vars with
          | [] -> -8 
          | not_empty_list ->
            (snd (List.nth  not_empty_list 0) - 8)
        in
        let stack_memory_allocated =
          match stack_memory_allocated < - offest with 
          (* grows stack downwards for 24 bytes, takes 8 for newmade var *)
          |true -> let stack_memmory_gain = 24 in
            Printf.printf "addi sp, sp, -%d\n" stack_memmory_gain;
            stack_memory_allocated + 24;
          |false -> stack_memory_allocated
        in
        let vars = (id, offest) :: vars in
        Printf.printf "sd a0, %d(s0)\n" offest;
        codegen_statements tail vars stack_memory_allocated

  and codegen_wdd_and_tail ((comp, st, pos), tail) vars stack_memory_allocated = 
    (* labels contain position of start of the loop, so they are unique for each loop *)
    let start_label = Printf.sprintf ".while_%d_lbl" pos in
    let end_label = Printf.sprintf ".done_%d_lbl" pos in
    Printf.printf "%s:\n" start_label;
    codegen_branching comp vars end_label;
    codegen_statements st vars stack_memory_allocated;
    Printf.printf "addi sp, s0, -%d\n" stack_memory_allocated; 
    Printf.printf "j %s\n%s:\n" start_label end_label;
    codegen_statements tail vars stack_memory_allocated;

  and codgen_itef_and_tail itef tail vars stack_memory_allocated =
    let comp, then_branch, else_branch, pos = itef in
    let start_label = Printf.sprintf ".if_%d_lbl" pos in 
    let else_label = Printf.sprintf ".else_%d_lbl" pos in
    let fi_label = Printf.sprintf ".fi_%d_lbl" pos in
      Printf.printf "%s:\n" start_label;
      codegen_branching comp vars else_label;
      codegen_statements then_branch vars stack_memory_allocated;
      Printf.printf "addi sp, s0, -%d\n" stack_memory_allocated;
      Printf.printf "j %s\n%s:\n" fi_label else_label;
      codegen_statements else_branch vars stack_memory_allocated;
      Printf.printf "addi sp, s0, -%d\n" stack_memory_allocated; 
      Printf.printf "%s:\n" fi_label;
      codegen_statements tail vars stack_memory_allocated

  and codegen_branching comparision vars else_branch_label =
    let Comparision (comp_op, expr1, expr2) = comparision in
    codegen_expr expr1 vars;
    codegen_expr ~reg:1 expr2 vars;
    let branching_op =
      match comp_op with
      | Not_equal -> "beq"
      | Equal -> "bne"
      | Less_or_equal -> "bgt"
      | Less -> "bge"
      | Greater_or_equal -> "blt"
      | Greater -> "ble"
    in
      Printf.printf "%s a0, a1, %s\n" branching_op else_branch_label
  (* defines type of first statement in list and calls corresponding codegen func *)
  and codegen_statements statements vars stack_memory_allocated =
    match statements with
    | Assignment_and_tail (assignment, tail) ->
      codegen_assignment_and_tail assignment tail vars stack_memory_allocated;
    | While_Do_Done_and_tail ((comp, st, pos), tail) ->
      codegen_wdd_and_tail ((comp, st, pos), tail) vars stack_memory_allocated;
    | Nothing -> ()
    | If_Then_Else_Fi_and_tail (itef, tail) ->
      codgen_itef_and_tail itef tail vars stack_memory_allocated 

  in
  let stack_memory_allocated = 24 in
  Printf.printf ".global _start\n\n_start:\n";
  (* grows stack downwards and sets stack pointer to first address in stack *)
  Printf.printf "addi sp, sp, -%d\naddi s0, sp, %d\n" stack_memory_allocated stack_memory_allocated;
  codegen_statements program [] stack_memory_allocated;
  (*while only assignment and expressions are implemented: the line below returns <last var> % 256*)
  Printf.printf "li a1, 256\nrem a0, a0, a1\nli a7, 93\necall" 
