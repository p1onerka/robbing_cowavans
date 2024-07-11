type oper = Plus | Multiply | Divide

(* tree construction for every expression which can be const or expr (then root is statement) *)
type expr =
    | Const of int
    | Var of string
    | Binop of oper * expr * expr

let find_len s = 
  String.length s

let is_digit c = c >= '0' && c <= '9'

let is_whitespace c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

let ws text pos =
  let length = find_len text in
  let rec skip pos =
    if pos < length && is_whitespace text.[pos] then skip (pos + 1)
    else pos
  in
  skip pos

let econst text pos =
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

let ident_or_keyword text pos =
  let length = find_len text in
  let rec acc_id pos acc =
    if pos < length && is_alpha text.[pos] then
      acc_id(pos + 1) (acc ^ String.make 1 text.[pos])
    else
      if String.length acc > 0 then
        `Success (acc, pos)
      else
        `Error
  in
  acc_id pos ""

let is_keyword s =
  s = "while" || s = "do" || s = "done" || s = "if" || s = "then" || s = "else"

let ident text pos =
  match ident_or_keyword text pos with
  | `Success (s, new_pos) ->
      if is_keyword s then
        `Error
      else
        `Success (Var s, new_pos)
  | `Error -> `Error

(* expression is name for terms connected with + *)
let rec expr text pos =
  let pos = ws text pos in
  match term text pos with
  | `Error -> `Error
  | `Success (left, pos) -> expr_tail left text pos

and expr_tail left text pos =
  let pos = ws text pos in
  if pos < find_len text && text.[pos] = '+' then
    match term text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> expr_tail (Binop (Plus, left, right)) text pos
  else
  (* expression can be single term *)
    `Success (left, pos)

(* term is name for some factors connected with *\ *)
and term text pos =
  let pos = ws text pos in
  match factor text pos with
  | `Error -> `Error
  | `Success (left, pos) -> term_tail left text pos

and term_tail left text pos =
  let pos = ws text pos in
  if pos < find_len text && text.[pos] = '*' then
    match factor text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> term_tail (Binop (Multiply, left, right)) text pos
  else
    `Success (left, pos)

(* factor is name for atomic term: const, var, smth in brackets *)
(* main idea is that factors are calculated to the time of operation *)
and factor text pos =
  let pos = ws text pos in
  (* expr in brackets *)
  if pos < find_len text && text.[pos] = '(' then
    (Printf.printf "here %d \n" pos;
    match expr text (pos + 1) with
    | `Error -> `Error
    | `Success (e, pos) ->
        let pos = ws text pos in
        if pos < find_len text && text.[pos] = ')' then
          `Success (e, pos + 1)
        else
          `Error)
  (* single const *)
  else if pos < find_len text && is_digit text.[pos] then
    econst text pos
  (* identificator aka var *)
  else if pos < find_len text && is_alpha text.[pos] then
    ident text pos
  (* unknown shit *)
  else
    `Error

let rec print_expr_levels expr level =
  match expr with
  | Const n -> Printf.printf "%sConst %d\n" (String.make (level * 2) ' ') n
  | Var v -> Printf.printf "%sVar %s\n" (String.make (level * 2) ' ') v
  | Binop (op, left, right) ->
      Printf.printf "%sBinop %s\n" (String.make (level * 2) ' ') 
        (match op with Plus -> "+" | Multiply -> "*" | Divide -> "/");
      print_expr_levels left (level + 1);
      print_expr_levels right (level + 1)

let parse_and_print text =
  match expr text 0 with
  | `Error -> Printf.printf "Error parsing expression\n"
  | `Success (ast, pos) -> 
      print_expr_levels ast 0

(* example *)
let () =
  let input = "1+3+4+(5" in
  parse_and_print input

