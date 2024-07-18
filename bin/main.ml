open Parser.Readfile 
open Codegen_riscv64.Codegen

(* EXAMPLES/test calls, need to be removed later *)

(* let () =
  let input = read_file_as_string "test/test_input.txt" in
  parse_and_print input *)

  (* outside parser calling inside parsers of assignment, while or if 
     if any of them is true than call outside parser from current inside position
     else try another inside parser from starting position
    *)

(*comparision examples *)
(* let() =
  let input = read_file_as_string "test/test_comporision1_input.txt" in
    parse_and_print_comparision input 
(* let() =
  let input = read_file_as_string "test/test_comporision2_input.txt" in
    parse_and_print_comparision input *) *)
(* statements/program example *)
(* let () =
     parse_and_print_program "test/test_full_program_input.txt"  *)

(* assignments and expressions codegen example *)
let() =
    if Array.length Sys.argv < 2 then failwith 
      "expects 1 argument, but is applied here to 0 argumens";
    (* parse_and_print_program Sys.argv.(1); *)
    match program Sys.argv.(1) with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog
