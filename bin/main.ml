open Parser.Readfile 
(*open Codegen_riscv64.Codegen*)
open Parser.Error_processing
open Parser.Statement_parser
(*open Parser.Const_simplification*)
open Parser.Types

let rec print_expr_levels expr level =
  match expr with
  | Const n -> Printf.printf "%sConst %s\n" (String.make (level * 2) ' ') n
  | Var (Ident (v, _)) -> Printf.printf "%sVar %s\n" (String.make (level * 2) ' ') v
  | Binop (op, left, right) ->
      Printf.printf "%sBinop %s\n" (String.make (level * 2) ' ')
        (match op with Plus -> "+" | Minus -> "-" | Multiply -> "*" | Divide -> "/");
      print_expr_levels left (level + 1);
      print_expr_levels right (level + 1)

let print_comparison_levels comparison level =
  let Comparision (c_op, left, right) = comparison in
  Printf.printf "%sComparison %s\n" (String.make (level * 2) ' ')
    (match c_op with
    | Equal -> "="
    | Less -> "<"
    | Greater -> ">"
    | Not_equal -> "<>"
    | Less_or_equal -> "<="
    | Greater_or_equal -> ">=");
  print_expr_levels left (level + 1);
  print_expr_levels right (level + 1)

let rec print_statements_levels statements level =
  match statements with
  | Assignment_and_tail ((Ident (ident, _), expr), tail) ->
    Printf.printf "%sAssignment_and_tail\n" (String.make (level * 2) ' ');
    Printf.printf "%s%s\n" (String.make ((level + 1) * 2) ' ') ident;
    print_expr_levels expr (level + 1);
    print_statements_levels tail (level + 1)
  | While_Do_Done_and_tail ((comp, st, _), tail) -> 
    Printf.printf "%sWhile_Do_Done_and_tail\n" (String.make (level * 2) ' ');
    print_comparison_levels comp (level + 1);
    print_statements_levels st (level + 1);
    print_statements_levels tail (level + 1)
  | If_Then_Else_Fi_and_tail ((comp, st1, st2, _), tail) ->
    Printf.printf "%sIf_Then_Else_Fi_and_tail\n" (String.make (level * 2) ' ');
    print_comparison_levels comp (level + 1);
    print_statements_levels st1 (level + 1);
    print_statements_levels st2 (level + 1);
    print_statements_levels tail (level + 1)
  | Function_and_tail ((name, args, st), tail) ->
    Printf.printf "%sFunction_and_tail\n" (String.make (level * 2) ' ');
    Printf.printf "%sFunction name: %s\n" (String.make ((level + 1) * 2) ' ') name;
    List.iter (fun (Ident (arg, _)) -> Printf.printf "%sArg: %s\n" (String.make ((level + 2) * 2) ' ') arg) args;
    print_statements_levels st (level + 1);
    print_statements_levels tail (level + 1)
  | Return ((expr), tail) ->
    Printf.printf "%sReturn \n" (String.make (level * 2) ' ');
    print_expr_levels expr (level + 1);
    print_statements_levels tail (level + 1)
  | Nothing -> Printf.printf "%sNothing\n" (String.make (level * 2) ' ')


let() =
  let parse_and_codegen_program program_text =
    match find_statements program_text 0 EOF with
    | `Error (msg, pos) -> error_processing program_text msg pos
    | `Success (prog, _) -> 
      print_statements_levels prog 0;
      (* match codegen (simplify_statements prog) with 
      match codegen prog with
      |`Error (msg, pos) -> error_processing program_text msg pos
      | `Success _ -> () *)
  in
    if Array.length Sys.argv < 2 then failwith "expects 1 argument, recieved 2";
    let input = read_file_as_string Sys.argv.(1) in parse_and_codegen_program input;
    (* String.iteri (fun i ch -> (print_int i; print_string " "; print_char ch; print_string "\n")) input *)