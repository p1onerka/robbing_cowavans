(*
open Types

let rec collect_constants_addition acc = function
  | Binop (Plus, Const a, Const b) -> 
      let sum = (int_of_string a) + (int_of_string b) in
      Const (string_of_int sum) :: acc
  | Binop (Plus, Const a, right) -> 
      let sum = int_of_string a in
      collect_constants_addition (Const (string_of_int sum) :: acc) right
  | Binop (Plus, left, Const b) -> 
      let sum = int_of_string b in
      collect_constants_addition (Const (string_of_int sum) :: acc) left
  | Binop (Plus, left, right) -> 
      let left_constants = collect_constants_addition [] left in
      let right_constants = collect_constants_addition [] right in
      left_constants @ right_constants @ acc
  | expr -> expr :: acc

let rec sum_constants = function
  | [] -> Const "0"
  | [expr] -> expr
  | Const a :: Const b :: rest -> 
      sum_constants (Const (string_of_int ((int_of_string a) + (int_of_string b))) :: rest)
  | expr :: rest -> Binop (Plus, expr, sum_constants rest)

let rec collect_constants_sub acc = function
  | Binop (Minus, Const a, Const b) -> 
      let sub = (int_of_string a) - (int_of_string b) in
      Const (string_of_int sub) :: acc
  | Binop (Minus, Const a, right) -> 
      let sub = int_of_string a in
      collect_constants_sub (Const (string_of_int sub) :: acc) right
  | Binop (Minus, left, Const b) -> 
      let sub = int_of_string b in
      collect_constants_sub (Const (string_of_int sub) :: acc) left
  | Binop (Minus, left, right) -> 
      let left_constants = collect_constants_sub [] left in
      let right_constants = collect_constants_sub [] right in
      left_constants @ right_constants @ acc
  | expr -> expr :: acc

let rec sub_constants = function
  | [] -> Const "0"
  | [expr] -> expr
  | Const a :: Const b :: rest -> 
      sub_constants (Const (string_of_int ((int_of_string a) - (int_of_string b))) :: rest)
  | expr :: rest -> Binop (Minus, expr, sub_constants rest)

(* connect overflow processing? *)
let rec simplify_expr = function
  | Binop (Plus, left, right) ->
      let simplified_left = simplify_expr left in
      let simplified_right = simplify_expr right in
      let constants = collect_constants_addition [] (Binop (Plus, simplified_left, simplified_right)) in
      sum_constants constants
  | Binop (Minus, left, right) ->
      let simplified_left = simplify_expr left in
      let simplified_right = simplify_expr right in
      let constants = collect_constants_sub [] (Binop (Minus, simplified_left, simplified_right)) in
      sub_constants constants
      (*
      begin match (simplified_left, simplified_right) with
        | (Const a, Const b) ->
            let result = (int_of_string a) - (int_of_string b) in
            Const (string_of_int result)
        | _ -> Binop (Minus, simplified_left, simplified_right)
      end *)
  | Binop (Multiply, left, right) ->
      let simplified_left = simplify_expr left in
      let simplified_right = simplify_expr right in
      begin match (simplified_left, simplified_right) with
        | (Const a, Const b) ->
            let result = (int_of_string a) * (int_of_string b) in
            Const (string_of_int result)
        | _ -> Binop (Multiply, simplified_left, simplified_right)
      end
  | Binop (Divide, left, right) ->
      let simplified_left = simplify_expr left in
      let simplified_right = simplify_expr right in
      begin match (simplified_left, simplified_right) with
        | (Const a, Const b) ->
            let result = (int_of_string a) / (int_of_string b) in
            Const (string_of_int result)
        | _ -> Binop (Divide, simplified_left, simplified_right)
      end
  | other -> other

let simplify_comparison (Comparision (op, left, right)) =
  Comparision (op, simplify_expr left, simplify_expr right)

let rec simplify_statements = function
  | Assignment_and_tail ((ident, expr), tail) ->
      Assignment_and_tail ((ident, simplify_expr expr), simplify_statements tail)
  | While_Do_Done_and_tail ((comp, body, pos), tail) ->
      While_Do_Done_and_tail ((simplify_comparison comp, simplify_statements body, pos), simplify_statements tail)
  | If_Then_Else_Fi_and_tail ((comp, then_branch, else_branch, pos), tail) ->
      If_Then_Else_Fi_and_tail ((simplify_comparison comp, simplify_statements then_branch, simplify_statements else_branch, pos), simplify_statements tail)
  | Nothing -> Nothing

   ENDS HERE *) 
(*
let simplify_expr expr =
  let rec gather_constants_and_vars expr =
    match expr with
    | Const c -> (int_of_string c, [])
    | Var v -> (0, [Var v])
    | Binop (op, left, right) ->
      let (left_const, left_vars) = gather_constants_and_vars left in
      let (right_const, right_vars) = gather_constants_and_vars right in
      match op with
      | Plus -> (left_const + right_const, left_vars @ right_vars)
      | Minus -> (left_const - right_const, left_vars @ right_vars)
      | Multiply -> (left_const * right_const, left_vars @ right_vars)
      | Divide -> (left_const / right_const, left_vars @ right_vars)
  in
  let (total_const, vars) = gather_constants_and_vars expr in
  match vars with
  | [] -> Const (string_of_int total_const)
  | _ ->
    let simplified_expr = List.fold_left (fun acc v ->
      match acc with
      | None -> Some v
      | Some acc -> Some (Binop (Plus, acc, v))
    ) None vars in
    match simplified_expr with
    | None -> Const (string_of_int total_const)
    | Some e -> if total_const = 0 then e else Binop (Plus, Const (string_of_int total_const), e)


let rec simplify_statements stmts =
  match stmts with
  | Assignment_and_tail ((id, expr), tail) ->
    let simplified_expr = simplify_expr expr in
    Assignment_and_tail ((id, simplified_expr), simplify_statements tail)
  | While_Do_Done_and_tail ((comp, body, start_pos), tail) ->
    let simplified_comp = simplify_comparision comp in
    let simplified_body = simplify_statements body in
    While_Do_Done_and_tail ((simplified_comp, simplified_body, start_pos), simplify_statements tail)
  | If_Then_Else_Fi_and_tail ((comp, then_branch, else_branch, start_pos), tail) ->
    let simplified_comp = simplify_comparision comp in
    let simplified_then = simplify_statements then_branch in
    let simplified_else = simplify_statements else_branch in
    If_Then_Else_Fi_and_tail ((simplified_comp, simplified_then, simplified_else, start_pos), simplify_statements tail)
  | Nothing -> Nothing

and simplify_comparision (Comparision (op, left, right)) =
  Comparision (op, simplify_expr left, simplify_expr right)
*)
let simplify_const program = 
  program
  
