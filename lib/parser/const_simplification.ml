open Types

(* perform simplification of constants inside of arithmetical expressions
  for faster code generation *)

let rec simplify_expr = function
  | Binop (Plus, Const c1, Const c2) ->
    Const (string_of_int (int_of_string c1 + int_of_string c2))
  | Binop (Minus, Const c1, Const c2) ->
    Const (string_of_int (int_of_string c1 - int_of_string c2))
  | Binop (Multiply, Const c1, Const c2) ->
    Const (string_of_int (int_of_string c1 * int_of_string c2))
  | Binop (Divide, Const c1, Const c2) ->
    Const (string_of_int (int_of_string c1 / int_of_string c2))
  | Binop (op, left, right) -> 
    (match (simplify_expr left, simplify_expr right) with
    | (Const c1, Const c2) -> simplify_expr (Binop (op, Const c1, Const c2))
    | (simpl_left, simpl_right) -> Binop (op, simpl_left, simpl_right))
  | Func_Call (ident, expr_list) -> 
    Func_Call (ident, List.map simplify_expr expr_list)
  | expr -> expr

let rec simplify_statements = function
  | Assignment_and_tail ((ident, expr), tail) ->
    Assignment_and_tail ((ident, simplify_expr expr), simplify_statements tail)
  | While_Do_Done_and_tail ((comparision, (statements, ident_list), start_pos), tail) ->
    While_Do_Done_and_tail (
      (simplify_comparison comparision, 
       (simplify_statements statements, ident_list), start_pos), 
      simplify_statements tail)
  | If_Then_Else_Fi_and_tail ((comparision, (then_statements, then_ident_list), (else_statements, else_ident_list), start_pos), tail) ->
    If_Then_Else_Fi_and_tail (
      (simplify_comparison comparision, 
       (simplify_statements then_statements, then_ident_list), 
       (simplify_statements else_statements, else_ident_list), start_pos), 
      simplify_statements tail)
  | Function_and_tail ((ident, arg_list, (statements, ident_list)), tail) ->
    Function_and_tail (
      (ident, arg_list, (simplify_statements statements, ident_list)), 
      simplify_statements tail)
  | Return (expr, tail) ->
    Return (simplify_expr expr, simplify_statements tail)
  | Function_Call ((ident, expr_list), tail) ->
    Function_Call ((ident, List.map simplify_expr expr_list), simplify_statements tail)
  | Nothing -> Nothing

and simplify_comparison = function
  | Comparision (op, left, right) ->
    Comparision (op, simplify_expr left, simplify_expr right) 
