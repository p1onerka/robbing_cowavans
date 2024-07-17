open Types

let find_len s = String.length s

let is_digit c = c >= '0' && c <= '9'

let is_whitespace c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c == '_')

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
  let rec acc_num pos acc =
    if pos < length && is_digit text.[pos] then
      acc_num (pos + 1) (acc ^ String.make 1 text.[pos])
    else
      if String.length acc > 0 then
        `Success (Const (int_of_string acc), pos)
      else
        `Error
  in
  acc_num pos ""

let find_ident_or_keyword text pos =
  let pos = find_ws text pos in
  let length = find_len text in
  let rec acc_id pos acc =
    if pos < length && is_alpha text.[pos] then
      acc_id (pos + 1) (acc ^ String.make 1 text.[pos])
    else
      if String.length acc > 0 then
        `Success (acc, pos)
      else
        `Error
  in
  acc_id pos ""

let is_keyword s =
  s = "while" || s = "do" || s = "done" || s = "if" || s = "then" || s = "else" || s = "fi"

let find_ident text pos =
  match find_ident_or_keyword text pos with
  | `Success (s, new_pos) ->
      if is_keyword s then
        `Error
      else
        `Success (Var (Ident s), new_pos)
  | `Error -> `Error

(* expression is name for terms connected with +/- *)
let rec find_expr text pos =
  let pos = find_ws text pos in
  match find_term text pos with
  | `Error -> `Error
  | `Success (left, pos) -> find_expr_tail left text pos

(* here: tail is term or expr in brackets taking place after +/- *)
and find_expr_tail left text pos =
  let pos = find_ws text pos in
  if pos < find_len text && text.[pos] = '+' then
    match find_term text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> find_expr_tail (Binop (Plus, left, right)) text pos
  else if pos < find_len text && text.[pos] = '-' then
    match find_term text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> find_expr_tail (Binop (Minus, left, right)) text pos
  else
  (* expression can be single term *)
    `Success (left, pos)

(* term is name for some factors connected with *\/ *)
and find_term text pos =
  let pos = find_ws text pos in
  match find_factor text pos with
  | `Error -> `Error
  | `Success (left, pos) -> find_term_tail left text pos

and find_term_tail left text pos =
  let pos = find_ws text pos in
  if pos < find_len text && text.[pos] = '*' then
    match find_factor text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> find_term_tail (Binop (Multiply, left, right)) text pos
  else if pos < find_len text && text.[pos] = '/' then
    match find_factor text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> find_term_tail (Binop (Divide, left, right)) text pos
  else
    `Success (left, pos)

(* factor is name for atomic term: const, var, smth in brackets *)
and find_factor text pos =
  let pos = find_ws text pos in
  (* expr in brackets *)
  if pos < find_len text && text.[pos] = '(' then
    match find_expr text (pos + 1) with
    | `Error -> `Error
    | `Success (e, pos) ->
        let pos = find_ws text pos in
        if pos < find_len text && text.[pos] = ')' then
          `Success (e, pos + 1)
        else
          `Error
  (* single const *)
  else if pos < find_len text && is_digit text.[pos] then
    find_const text pos
  (* identificator aka var *)
  else if pos < find_len text && is_alpha text.[pos] then
    find_ident text pos
  (* unknown token *)
  else
    `Error