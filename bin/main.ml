open Parser.Readfile 
open Codegen_riscv64.Codegen
open Parser.Error_processing
open Parser.Statement_parser

let() =
  let parce_and_codegen_program program_text =
    match find_statements program_text 0 EOF with
    | `Error (msg, pos) -> error_processing program_text msg pos
    | `Success (prog, _) -> match codegen prog with 
      |`Error (msg, pos) -> error_processing program_text msg pos
      | `Success _ -> ()
  in
    if Array.length Sys.argv < 2 then failwith "expects 1 argument, recieved 2";
    let input = read_file_as_string Sys.argv.(1) in parce_and_codegen_program input