open Types
open Expression_parser

(* Pascal-like: [=] - equal, [<>] - not equal, [<], [<=], [>], [>=]  *)
   let find_comp_oper text pos =
    let find_after_less_oper =
      if pos + 1 >= find_len text then `Success (Less, pos)
      else match text.[pos + 1] with
      | '>' -> `Success (Not_equal, pos + 2)
      | '=' -> `Success (Less_or_equal, pos + 2)
      | _ -> `Success (Less, pos + 1)
    in
    let find_after_right_oper =
      if pos + 1 >= find_len text then `Success (Greater, pos)
      else match text.[pos + 1] with
      | '=' -> `Success (Greater_or_equal, pos + 2)
      | _ -> `Success (Greater, pos + 1)
    in
    let pos = find_ws text pos in
    if pos >= find_len text then `Error
    else match text.[pos] with 
      | '=' -> `Success (Equal, pos + 1)
      | '<' -> find_after_less_oper
      | '>' -> find_after_right_oper
      | _ -> `Error

(* take first expr, try to find comp oper, 
   combine it with second expr to form comparison *)
let find_comparision text pos =
  match find_expr text pos with 
  | `Error -> `Error ("Condition scheme invalid. Some expressions may have been entered incorrectly", pos)
  | `Success (e1, pos) ->
    match find_comp_oper text pos with
    | `Error -> `Error ("Condition scheme invalid. An incorrect comparison operator may have been entered", pos)
    | `Success (c_op, pos) -> 
      match find_expr text pos with
      | `Error -> `Error ("Condition scheme invalid. Some expressions may have been entered incorrectly", pos)
      | `Success (e2, pos)-> `Success (Comparision (c_op, e1, e2), pos)

type end_marker = EOF | Word of string

(* wdd = while-do-done, itef = if-then-else-fi *)
(* defines kind of statement by starting keyword 
   and calls corresponding func *)
let rec find_statements text pos end_marker =
  let pos = find_ws text pos in
  if pos >= find_len text && end_marker == EOF then `Success (Nothing, pos)
  else match find_ident_or_keyword text pos with
    | `Error -> `Error ("Syntax error occured, the code doesn't match any scheme. The code block may not have been completed correctly", pos)
    | `Success (id_or_kw, pos) ->
      match Word id_or_kw with
      | em when em = end_marker -> `Success (Nothing, pos)
      | Word "while" -> wdd_and_tail text pos end_marker
      | Word "if" -> itef_and_tail text pos end_marker
      | Word id -> 
        if (is_keyword id) then `Error ("Unidentified or incorrect keyword", pos)
        else assignment_and_tail text pos (Ident id) end_marker
      | EOF -> `Error ("Unexpected end of input", pos)(* unreacheable *) 
       
(* (Ksenia): second version, wanna save it until im sure it is useless :)
and parse_assignment text pos ident prev_end_marker =
  let pos = find_ws text pos in
  if pos < find_len text && text.[pos] = ':' && pos + 1 < find_len text && text.[pos + 1] = '=' then
    let pos = find_ws text (pos + 2) in
    match expr text pos with
    | `Error -> `Error
    | `Success (e, pos) ->
        let pos = find_ws text pos in
        if pos < find_len text && text.[pos] = ';' then
          `Success (Assignment_and_tail ((ident, e), Nothing), pos + 1)
        else
          `Error
  else
    `Error

and assignment_and_tail text pos id prev_end_marker =
  match parse_assignment text pos id prev_end_marker with
  | `Error -> `Error
  | `Success (assignment, pos) ->
      match statements text pos prev_end_marker with
      | `Error -> `Error
      | `Success (tail, pos) ->
          `Success (Assignment_and_tail ((id, match assignment with Assignment_and_tail ((_, e), _) -> e | _ -> failwith "Unreachable"), tail), pos)
*)

and assignment_and_tail text pos ident prev_end_marker =
let pos = find_ws text pos in
if pos + 1 < find_len text && text.[pos] = ':' && text.[pos + 1] = '=' then
  let pos = find_ws text (pos + 2) in
  match find_expr text pos with
  | `Error -> `Error ("Empty assignment found. Please enter some expression", pos)
  | `Success (exp, pos) ->
    let pos = find_ws text pos in
    if pos < find_len text && text.[pos] = ';' then
      let pos = find_ws text (pos + 1) in
      match find_statements text pos prev_end_marker with
      | `Error (msg, pos) -> `Error (msg, pos)
      | `Success (st, pos) ->
        `Success (Assignment_and_tail ((ident, exp), st), pos)
    else `Error ("Couldn't find ; in assignment", pos)
else `Error ("Couldn't find := in assignment", pos)


(* forms a statement out of first found comparison 
   and given start/end marker (which are common part of wdd/ited statements) to define the statement. 
   Additionaly forms tree of nested statements *)
and find_comp_and_nested_statements text pos statements_start_word statements_end_marker = 
  match find_comparision text pos with
  | `Error (msg, pos) -> `Error (msg, pos)
  | `Success (comp_tree, pos) ->
    (match find_ident_or_keyword text pos with
    | `Success (ssw, pos) when ssw = statements_start_word ->
      (match find_statements text pos statements_end_marker with
      | `Error (msg, pos) -> `Error (msg, pos)
      | `Success (st, pos)-> `Success (comp_tree, st, pos))
    | _ -> `Error ("Syntax error occured. The code doesn't match any scheme", pos))

(* parses completely insides of wdd/itef statement and forms its "tail":
   link to next statement of program on current level (in current block) *)
and wdd_and_tail text pos prev_end_marker = 
  let start_pos = pos in
  match find_comp_and_nested_statements text pos "do" (Word "done") with
  | `Error (msg, pos) -> `Error (msg, pos)
  | `Success (comp_tree, st, pos)->
    match find_statements text pos prev_end_marker  with
    | `Error (msg, pos) -> `Error (msg, pos)
    | `Success (tail, pos) -> 
      `Success (While_Do_Done_and_tail ((comp_tree, st, start_pos), tail), pos)

and itef_and_tail text pos prev_end_marker =
  let start_pos = pos in 
  match find_comp_and_nested_statements text pos "then" (Word "else") with
  | `Error (msg, pos) -> `Error (msg, pos)
  | `Success (comp_tree, st1, pos)-> 
    (match find_statements text pos (Word "fi") with
    | `Error (msg, pos) -> `Error (msg, pos)
    | `Success (st2, pos)->
      (match find_statements text pos prev_end_marker  with
      | `Error (msg, pos) -> `Error (msg, pos)
      | `Success (tail, pos) -> 
        `Success (If_Then_Else_Fi_and_tail ((comp_tree, st1, st2, start_pos), tail), pos)))
