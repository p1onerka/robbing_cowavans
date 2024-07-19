open Statement_parser
(* there are also debug prints, dont forget to delete them later *)

let read_file_as_string filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let program file_name =
  let input = read_file_as_string file_name in
    find_statements input 0 EOF

(* debug print functions, need to be removed later *)

(*
let rec print_expr_levels expr level =
  match expr with
  | Const n -> Printf.printf "%sConst %d\n" (String.make (level * 2) ' ') n
  | Var Ident v -> Printf.printf "%sVar %s\n" (String.make (level * 2) ' ') v
  | Binop (op, left, right) ->
      Printf.printf "%sBinop %s\n" (String.make (level * 2) ' ') 
        (match op with Plus -> "+" | Minus -> "-" | Multiply -> "*" | Divide -> "/");
      print_expr_levels left (level + 1);
      print_expr_levels right (level + 1) 

 let parse_and_print text =
  match find_expr text 0 with
  | `Error -> Printf.printf "Error parsing expression\n"
  | `Success (ast, _) -> 
    print_expr_levels ast 0


let print_comporision_levels comparision level =
  let Comparision (c_op, left, right) = comparision in
  Printf.printf "%sComporision %s\n" (String.make (level * 2) ' ')
  ( match (c_op) with
  | Equal-> "="
  | Less -> "<"
  | Greater -> ">"
  | Not_equal -> "<>"
  | Less_or_equal -> "<="
  | Greater_or_equal -> ">="
  );
  print_expr_levels left (level + 1);
  print_expr_levels right (level + 1)

(* let parse_and_print_comparision text  =
  match find_comparision text 0 with
  | `Error -> Printf.printf "Error parsing comporission\n"
  | `Success (comparision, _) -> 
    print_comporision_levels comparision 0
*)
let rec print_statements_levels statements level =
  match statements with
  | While_Do_Done_and_tail ((comp, st, _), tail) -> 
    Printf.printf "%sWhileDoDone_and_tail\n" (String.make (level * 2) ' ');
    print_comporision_levels comp (level + 1);
    print_statements_levels st (level + 1);
    print_statements_levels tail (level + 1)
  | If_Then_Else_Fi_and_tail ((comp, st1, st2, _), tail) ->
    Printf.printf "%sIfThenElseFi_and_tail\n" (String.make (level * 2) ' ');
    print_comporision_levels comp (level + 1);
    print_statements_levels st1 (level + 1);
    print_statements_levels st2 (level + 1);
    print_statements_levels tail (level + 1)
  | Assignment_and_tail ((Ident (ident), expr), tail) ->
    Printf.printf "%sAssignment_and tail\n" (String.make (level * 2) ' ');
    Printf.printf "%s%s\n" (String.make ((level + 1) * 2) ' ') ident;
    print_expr_levels expr (level + 1);
    print_statements_levels tail (level + 1)
  | Nothing -> Printf.printf "%s%s\n" (String.make (level * 2) ' ') "Nothing"

let parse_and_print_program file_name =
  match program file_name with
  | `Error -> Printf.printf "Error parsing programm\n"
  | `Success (statements,_) -> 
    print_statements_levels statements 0 
*)