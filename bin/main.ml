open Parser.Readfile 
open Codegen_riscv64.Codegen

let() =
    if Array.length Sys.argv < 2 then failwith 
      "expects 1 argument, recieved 2";
    match program Sys.argv.(1) with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog
