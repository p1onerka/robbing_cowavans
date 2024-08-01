open Types
open Helpers.Bind

let find_len s = String.length s

let is_digit c = c >= '0' && c <= '9'

let is_whitespace c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c = '_')

(* ws = whitespaces *)
let find_ws text pos =
  let length = find_len text in
  let rec skip pos =
    if pos < length && is_whitespace text.[pos] then skip (pos + 1)
    else pos
  in
  skip pos

let find_const text pos =
  let length = find_len text in
  let overflow_check acc is_negative =
    let len = find_len acc in
      if len > 19 then `Error ("int overflow was found", pos)
      else if len < 19 then `Success (Const (acc))
      else 
        let (int_max_value_uppers, int_max_value_lowers) = 
          (9223372036, 854775807) in
        let (uppers, lowers) =
         (int_of_string (String.sub acc 0 10), int_of_string (String.sub acc 10 9))
        in
          if uppers > int_max_value_uppers ||
            (uppers = int_max_value_uppers && lowers > int_max_value_lowers)
          then `Error ("int overflow was found", pos)
          else 
            let acc = match is_negative with
              | true -> (Printf.sprintf "-") ^ acc
              | false -> acc in
                `Success (Const (acc)) 
  in
    let find_abs is_negative pos  =
      let rec acc_num pos acc =
        if pos < length && is_digit text.[pos] then
          acc_num (pos + 1) (acc ^ String.make 1 text.[pos])
        else
        if String.length acc > 0 then
          let* const = overflow_check acc is_negative in
            `Success(const, pos)
        else
        `Error ("", pos)
      in
        acc_num pos "" in
          if pos < length && text.[pos] = '-' then 
            find_abs true (find_ws text pos+1)
          else find_abs false pos

(* ident is any word that is not keyword, for example, variable or function name *)
let find_ident_or_keyword text pos =
  let pos0 = find_ws text pos in
  let length = find_len text in
  let rec acc_id pos acc =
    if pos < length && (is_alpha text.[pos] || text.[pos] == '}' || text.[pos] == '{') then
      acc_id (pos + 1) (acc ^ String.make 1 text.[pos])
    else
      if String.length acc > 0 then
        `Success (acc, pos)
      else
        `Error ("", pos0)
  in
  acc_id pos0 ""

let is_keyword s =
  s = "while" || s = "do" || s = "done" || s = "if" || s = "then" 
    || s = "else" || s = "fi" || s = "func" || s = "{" || s = "}"

let find_ident text pos0 =
  let* (s, pos) = find_ident_or_keyword text pos0 in
    if is_keyword s then
      `Error ("", pos0)
    else
      `Success (Var (Ident (s, pos0)), pos)

(* expression is name for terms connected with +/- *)
let rec find_expr text pos =
  let* (left, pos) = find_term text (find_ws text pos) in find_expr_tail left text pos

(* here: tail is term or expr in brackets taking place after +/- *)
and find_expr_tail left text pos0 =
  let pos = find_ws text pos0 in
  if pos < find_len text && text.[pos] = '+' then
    let* (right, pos) =  find_term text (pos + 1) in
      find_expr_tail (Binop (Plus, left, right)) text pos
  else if pos < find_len text && text.[pos] = '-' then
    let* (right, pos) = find_term text (pos + 1) in
      find_expr_tail (Binop (Minus, left, right)) text pos
  else
  (* expression can be single term *)
    `Success (left, pos0)

(* term is name for some factors connected with *\/ *)
and find_term text pos =
  let* (left, pos) = find_factor text (find_ws text pos) in
    find_term_tail left text pos

and find_term_tail left text pos0 =
  let pos = find_ws text pos0 in
  if pos < find_len text && text.[pos] = '*' then
    let* (right, pos) =  find_term text (pos + 1) in
      find_term_tail (Binop (Multiply, left, right)) text pos
  else if pos < find_len text && text.[pos] = '/' then
    let* (right, pos) =  find_term text (pos + 1) in
      find_term_tail (Binop (Divide, left, right)) text pos
  else
    `Success (left, pos0)

and find_arguments_in_call text pos =
  let pos = find_ws text pos in
  if pos < find_len text && text.[pos] = ')' then
    `Success ([], pos + 1)
  else
    let* (arg, pos) = find_expr text pos in
    let pos = find_ws text pos in
    if pos < find_len text && text.[pos] = ',' then
      let* (args, pos) = find_arguments_in_call text (pos + 1) in
      `Success (arg :: args, pos)
    else if pos < find_len text && text.[pos] = ')' then
      `Success (arg :: [], pos + 1)
    else
      `Error ("", pos) 

(* factor is name for atomic term: const, var, smth in brackets *)
and find_factor text pos =
  let pos = find_ws text pos in
  (* expr in brackets *)
  if pos < find_len text && text.[pos] = '(' then
    let* (e, pos) = find_expr text (pos + 1) in
      let pos = find_ws text pos in
        if pos < find_len text && text.[pos] = ')' then
          `Success (e, pos + 1)
        else
          `Error ("", pos) 
  (* single const *)
  else if pos < find_len text && (is_digit text.[pos] || text.[pos] = '-') then
    find_const text pos
  (* identificator: var OR function call *)
  else if pos < find_len text && is_alpha text.[pos] then
    match find_ident text pos with
    |`Error (msg, pos) -> `Error (msg, pos)
    |`Success (Var(ident), pos) ->
      let pos = find_ws text pos in
      if pos < find_len text && text.[pos] = '(' then
        let* (args, pos) = find_arguments_in_call text (pos + 1) in
        `Success (Func_Call (ident, args), pos)
      else 
        `Success (Var(ident), pos)
    |`Success _ -> `Error ("Expected variable as identifier", pos)
  else if pos < find_len text && text.[pos] = '-' then
    let* (expr, pos) = find_expr text (pos + 1) in
    `Success (Binop (Minus, Const "0", expr), pos)

  (* unknown token *)
  else
    `Error ("", pos)