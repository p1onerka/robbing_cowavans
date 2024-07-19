open Parser.Readfile 
open Codegen_riscv64.Codegen

(* DEGUB IN-PROGRAM TEST CALLS, need to be removed later *)

(* full programs tests *)
(* let () =
  match program "test/full_program_test1.txt" with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog *)
 (* let () =
  match program "test/full_program_test2.txt" with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog *)

(* comparision tests *)
(* let () =
  match program "test/comparison_test1.txt" with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog
(* let () =
  match program "test/comparison_test2.txt" with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog *) *)

(* assignment test *)
(* let () =
  match program "test/assignment_test.txt" with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog  *)


let() =
    if Array.length Sys.argv < 2 then failwith 
      "expects 1 argument, recieved 2";
    match program Sys.argv.(1) with
    |`Error -> failwith ""
    | `Success (prog,_) -> codegen prog
