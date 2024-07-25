open Types
open Expression_parser
open Helpers.Bind

(* Pascal-like: [=] - equal, [<>] - not equal, [<], [<=], [>], [>=]  *)
   let find_comp_oper text pos0 =
    let find_after_less_oper pos =
      if pos + 1 >= find_len text then `Success (Less, pos)
      else match text.[pos + 1] with
      | '>' -> `Success (Not_equal, pos + 2)
      | '=' -> `Success (Less_or_equal, pos + 2)
      | _ -> `Success (Less, pos + 1)
    in
    let find_after_right_oper pos =
      if pos + 1 >= find_len text then `Success (Greater, pos)
      else match text.[pos + 1] with
      | '=' -> `Success (Greater_or_equal, pos + 2)
      | _ -> `Success (Greater, pos + 1)
    in
    let pos = find_ws text pos0 in
    if pos >= find_len text then `Error ("", pos0)
    else match text.[pos] with 
      | '=' -> `Success (Equal, pos + 1)
      | '<' -> find_after_less_oper pos
      | '>' -> find_after_right_oper pos
      | _ -> `Error ("", pos)

(* take first expr, try to find comp oper, 
   combine it with second expr to form comparison *)
let find_comparision text pos =
  (* match find_expr text pos with 
  | `Error (_,pos) -> `Error ("Condition scheme invalid. Some expressions may have been entered incorrectly", pos)
  | `Success (e1, pos) -> *)
  let** (e1, pos) = 
    (find_expr text pos),
    "Condition scheme invalid. Some expressions may have been entered incorrectly"
  in
    let** (c_op, pos) = 
      (find_comp_oper text pos),
      "Condition scheme invalid. An incorrect comparison operator may have been entered" 
    in
        let** (e2, pos) = 
          (find_expr text pos),
         "Condition scheme invalid. Some expressions may have been entered incorrectly"
        in
         `Success (Comparision (c_op, e1, e2), pos)

type end_marker = EOF | Word of string

(* wdd = while-do-done, itef = if-then-else-fi *)
(* defines kind of statement by starting keyword 
   and calls corresponding func *)
let rec find_statements text pos end_marker =
  let pos = find_ws text pos in
  if pos >= find_len text then
    match end_marker with
    | EOF -> `Success (Nothing, pos)
    | Word w ->  `Error (Printf.sprintf "Syntax error occured. Expected '%s' but eof was reached" w, pos) 
  else match find_ident_or_keyword text pos with
    | `Error _ -> `Error ("Syntax error occured, the code doesn't match any scheme. The code block may not have been completed correctly", pos)
    | `Success (id_or_kw, pos1) ->
      match Word id_or_kw with
      | em when em = end_marker -> `Success (Nothing, pos1)
      | Word "while" -> wdd_and_tail text pos1 end_marker
      | Word "if" -> itef_and_tail text pos1 end_marker
      | Word "func" -> func_and_tail text pos1 end_marker
      | Word id -> 
        if (is_keyword id) then
          (let msg_expected_part = match end_marker with
            |EOF -> ""
            | Word w -> Printf.sprintf " (expected '%s') " w in
            `Error ("Unidentified or incorrect keyword" ^ msg_expected_part, pos))
        else assignment_and_tail text pos1 (Ident (id, pos)) end_marker
      | EOF -> `Error ("Unexpected end of input", pos1)(* unreacheable *) 
(*
and find_args text pos = 

and func_and_tail text pos prev_end_marker = 
  let pos = find_ws text pos in 
  match find_ident text pos with
  |`Success(name, pos) ->
    (if text.[pos] = '(' then 
      find_args text pos
    else 
      `Error ("Arguments should be in breackets", pos))
  |`Error(_, pos) -> `Error ("function should have name", pos) *)

and find_args text pos = 
  let pos = find_ws text pos in
  let rec parse_args pos acc =
    let pos = find_ws text pos in
    if pos >= find_len text then `Error ("Unexpected end of input while parsing arguments", pos)
    else if text.[pos] = ')' then `Success (List.rev acc, pos + 1)
    else
      match find_ident text pos with
      | `Success (Var(arg), pos) ->
          let pos = find_ws text pos in
          if pos < find_len text && text.[pos] = ',' then
            parse_args (pos + 1) (arg :: acc)
          else if pos < find_len text && text.[pos] = ')' then
            `Success (List.rev (arg :: acc), pos + 1)
          else `Error ("Invalid argument list", pos)
      | `Success (Const _, pos) ->
          `Error ("Argument cannot be a constant", pos)
      | `Success (Binop (_, _, _), pos) ->
          `Error ("Argument cannot be a binary operation", pos)
      | `Error _ -> `Error ("Invalid argument name", pos)
  in
  if text.[pos] = '(' then parse_args (pos + 1) []
  else `Error ("Expected '(' at the beginning of argument list", pos)

and parse_func_body text pos =
  let pos = find_ws text pos in
  if pos >= find_len text || text.[pos] <> '{' then `Error ("Expected '{' at the beginning of function body", pos)
  else
    let pos = find_ws text (pos + 1) in
    let* (body, pos) = find_statements text pos (Word "return") in
    let pos = find_ws text pos in 
    (*
    if pos + 6 <= find_len text && String.sub text pos 6 = "return" then
      let pos = find_ws text (pos + 6) in *)
      let* (ret_expr, pos) = find_expr text pos in
      let pos = find_ws text pos in
      if pos >= find_len text || text.[pos] <> '}' then
        `Error ("Expected '}' at the end of function body", pos)
      else
        `Success (body, ret_expr, pos + 1)
    (*else
      `Error ("Expected 'return' in function body", pos)*)

and func_and_tail text pos prev_end_marker = 
  let pos = find_ws text pos in 
  match find_ident text pos with
  | `Success (Var(Ident(name, _)), pos) ->
    let** (args, pos) = (find_args text pos), "Function should have arguments in brackets" in
    let** (body, return_expr, pos) = (parse_func_body text pos), "Function body is not valid" in
    let* (tail, pos) = find_statements text pos prev_end_marker in
    `Success (Function_and_tail ((name, args, return_expr, body), tail), pos)
  | `Success (Const _, pos) ->
    `Error ("Function name cannot be a constant", pos)
  | `Success (Binop (_, _, _), pos) ->
    `Error ("Function name cannot be a binary operation", pos)
  | `Error _ -> `Error ("Function should have a name", pos)

and assignment_and_tail text pos ident prev_end_marker =
let pos = find_ws text pos in
  if pos + 1 < find_len text && text.[pos] = ':' && text.[pos + 1] = '=' then
    let pos = find_ws text (pos + 2) in
    (* match find_expr text pos with
    | `Error _-> `Error ("Empty assignment found. Please enter some expression", pos)
    | `Success (exp, pos1) -> *)
      let** (exp, pos1) = (find_expr text pos),
        "Empty assignment found. Please enter some expression"
      in
        let pos = find_ws text pos1 in
          if pos < find_len text && text.[pos] = ';' then
            let pos = find_ws text (pos + 1) in
              let* (st, pos) = find_statements text pos prev_end_marker in
                `Success (Assignment_and_tail ((ident, exp), st), pos)
          else `Error ("Couldn't find ; in assignment", pos1)
else `Error ("Couldn't find := in assignment", pos)

(* forms a statement out of first found comparison 
   and given start/end marker (which are common part of wdd/ited statements) to define the statement. 
   Additionaly forms tree of nested statements *)
and find_comp_and_nested_statements text pos statements_start_word statements_end_marker = 
  let* (comp_tree, pos) = find_comparision text pos in
    (match find_ident_or_keyword text pos with
    | `Success (ssw, pos) when ssw = statements_start_word ->
      let* (st, pos) =  find_statements text pos statements_end_marker in
        `Success (comp_tree, st, pos)
    | _ -> `Error ( Printf.sprintf "Syntax error occured.
     The code doesn't match any scheme. Expexted '%s' " statements_start_word, pos))

(* parses completely insides of wdd/itef statement and forms its "tail":
   link to next statement of program on current level (in current block) *)
and wdd_and_tail text pos prev_end_marker = 
  let start_pos = pos in
  let* (comp_tree, st, pos) = find_comp_and_nested_statements text pos "do" (Word "done") in
    let* (tail, pos) = find_statements text pos prev_end_marker in 
      `Success (While_Do_Done_and_tail ((comp_tree, st, start_pos), tail), pos)

and itef_and_tail text pos prev_end_marker =
  let start_pos = pos in 
  let* (comp_tree, st1, pos) = find_comp_and_nested_statements text pos "then" (Word "else") in
    let* (st2, pos) = find_statements text pos (Word "fi") in
      let* (tail, pos) = find_statements text pos prev_end_marker in 
        `Success (If_Then_Else_Fi_and_tail ((comp_tree, st1, st2, start_pos), tail), pos)
