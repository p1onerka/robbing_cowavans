open Parser.Readfile 
open Parser.Error_processing
open Codegen_riscv64.Codegen

let() =
    if Array.length Sys.argv < 2 then failwith 
      "expects 1 argument, recieved 2";
    match program Sys.argv.(1) with
    |`Error (msg, pos) -> error_processing Sys.argv.(1) msg pos
    | `Success (prog, _) -> codegen prog 
