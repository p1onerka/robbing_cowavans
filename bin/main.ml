open Parser.Readfile 
open Codegen_riscv64.Codegen
open Parser.Error_processing
open Parser.Statement_parser
open Parser.Const_simplification
open Parser.Types
(*
let rec print_expr_levels expr level =
  match expr with
  | Const n -> Printf.printf "%sConst %s\n" (String.make (level * 2) ' ') n
  | Var (Ident (v, _)) -> Printf.printf "%sVar %s\n" (String.make (level * 2) ' ') v
  | Binop (op, left, right) ->
      Printf.printf "%sBinop %s\n" (String.make (level * 2) ' ')
        (match op with Plus -> "+" | Minus -> "-" | Multiply -> "*" | Divide -> "/");
      print_expr_levels left (level + 1);
      print_expr_levels right (level + 1)
  | Func_Call (Ident(name, _), args) ->
    Printf.printf "%sFunction call\n" (String.make (level * 2) ' ');
    Printf.printf "%s%s\n" (String.make ((level + 1) * 2) ' ') name;
    List.iter (fun expr -> print_expr_levels expr ((level + 2))) args

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

let print_ident_int_list list =
  Printf.printf "LIST OF INSIDES: \n";
  List.iter (fun (Ident (ident, _), pos) ->
    Printf.printf " Ident: %s, Args: %d\n" ident pos 
  ) list

let rec print_statements_levels statements level =
  match statements with
  | Assignment_and_tail ((Ident (ident, _), expr), tail) ->
    Printf.printf "%sAssignment_and_tail\n" (String.make (level * 2) ' ');
    Printf.printf "%s%s\n" (String.make ((level + 1) * 2) ' ') ident;
    print_expr_levels expr (level + 1);
    print_statements_levels tail (level + 1)
  | While_Do_Done_and_tail ((comp, (st, ident_int_list), _), tail) -> 
    Printf.printf "%sWhile_Do_Done_and_tail\n" (String.make (level * 2) ' ');
    print_comparison_levels comp (level + 1);
    print_statements_levels st (level + 1);
    Printf.printf "WHILE ";
    print_ident_int_list ident_int_list;
    print_statements_levels tail (level + 1)
  | If_Then_Else_Fi_and_tail ((comp, (st1, ident_int_list1), (st2, ident_int_list2), _), tail) ->
    Printf.printf "%sIf_Then_Else_Fi_and_tail\n" (String.make (level * 2) ' ');
    print_comparison_levels comp (level + 1);
    print_statements_levels st1 (level + 1);
    Printf.printf "THEN BRANCH ";
    print_ident_int_list ident_int_list1;
    print_statements_levels st2 (level + 1);
    Printf.printf "ELSE BRANCH ";
    print_ident_int_list ident_int_list2;
    print_statements_levels tail (level + 1)
  | Function_and_tail ((Ident (name, _), args, (st, ident_int_list)), tail) ->
    Printf.printf "%sFunction_and_tail\n" (String.make (level * 2) ' ');
    Printf.printf "%sFunction name: %s\n" (String.make ((level + 1) * 2) ' ') name;
    List.iter (fun (Ident (arg, _)) -> Printf.printf "%sArg: %s\n" (String.make ((level + 2) * 2) ' ') arg) args;
    print_statements_levels st (level + 1);
    Printf.printf "FUNCTION ";
    print_ident_int_list ident_int_list;
    print_statements_levels tail (level + 1)
  | Return (expr, tail) ->
    Printf.printf "%sReturn \n" (String.make (level * 2) ' ');
    print_expr_levels expr (level + 1);
    print_statements_levels tail (level + 1)
  | Function_Call ((Ident (name, _), args), tail) -> 
    Printf.printf "%sFunction call\n" (String.make (level * 2) ' ');
    Printf.printf "%s%s\n" (String.make ((level + 1) * 2) ' ') name;
    List.iter (fun expr -> print_expr_levels expr ((level + 2) * 2)) args;
    print_statements_levels tail (level + 1)
  | Nothing -> Printf.printf "%sNothing\n" (String.make (level * 2) ' ') *)

(* check that main function exists and has 0 arguments *)
let check_main func_list end_pos =
  let rec find_main list =
    match list with
    | [] ->  `Error ("Main function not found or contains arguments", end_pos)
    | (Ident (name, pos), arg_count) :: tail ->
        if name = "main" && arg_count = 0 then `Success (Ident (name, pos))
        else find_main tail
  in
  find_main func_list 

let() =
  let parse_and_codegen_program program_text =
    match find_statements program_text 0 EOF 0 [] with
    | `Error (msg, pos) -> error_processing program_text msg pos
    | `Success (prog, prog_list, end_pos) -> 
      match check_main prog_list end_pos with
      | `Error (msg, pos) -> error_processing program_text msg pos
      | `Success (main_ident) ->
        let prog0 = simplify_statements prog in
        (*
        print_statements_levels prog0 0;
        Printf.printf "MAIN ";
        print_ident_int_list prog_list; *)
        match codegen prog0 prog_list main_ident with
        |`Error (msg, pos) -> error_processing program_text msg pos
        | `Success _ -> ()
  in
    if Array.length Sys.argv < 2 then failwith "expects 1 argument, recieved 2";
    let input = read_file_as_string Sys.argv.(1) in parse_and_codegen_program input;
