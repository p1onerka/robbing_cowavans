type ariphm_oper = Plus | Multiply | Divide

(* tree construction for every expression which can be const or expr (then root is statement) *)
type expr =
  | Const of int
  | Var of string
  | Binop of ariphm_oper * expr * expr

type comp_oper = 
  | Less
  | Greater
  | Less_or_equal
  | Greater_or_equal
  | Equal
  | Not_equal

type comparision = Comparision of comp_oper * expr * expr

let find_len s = 
  String.length s

let is_digit c = c >= '0' && c <= '9'

let is_whitespace c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c == '_')

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
  let pos = ws text pos in
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
  s = "while" || s = "do" || s = "done" || s = "if" || s = "then" || s = "else" || s = "fi"

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
    match expr text (pos + 1) with
    | `Error -> `Error
    | `Success (e, pos) ->
        let pos = ws text pos in
        if pos < find_len text && text.[pos] = ')' then
          `Success (e, pos + 1)
        else
          `Error
  (* single const *)
  else if pos < find_len text && is_digit text.[pos] then
    econst text pos
  (* identificator aka var *)
  else if pos < find_len text && is_alpha text.[pos] then
    ident text pos
  (* unknown token *)
  else
    `Error
(* Pascal-like: [=] - equal, [<>] - not equal, [<], [<=], [>], [>=]  *)
let bin_oper text pos =
  let after_less_oper  =
    let pos = ws text (pos + 1) in
      if pos >= find_len text then `Success (Less, pos)
      else match text.[pos] with
      | '>' -> `Success (Not_equal, pos + 1)
      | '=' -> `Success (Less_or_equal, pos + 1)
      | _ -> `Success (Less, pos)
  in
  let pos = ws text pos in
  if pos >= find_len text then `Error
  else match text.[pos] with 
    | '=' -> `Success (Equal, pos + 1)
    | '<' -> after_less_oper
    | '>' -> let pos = ws text (pos + 1) in
      if pos < find_len text && text.[pos] == '=' then
        `Success (Greater_or_equal, pos + 1)
      else `Success (Greater, pos)
    | _ -> `Error

let comparision text pos =
  match expr text pos with 
  | `Error -> `Error
  | `Success (e1, pos) ->
    match bin_oper text pos with
    | `Error -> `Error
    | `Success (c_op, pos) -> 
      match expr text pos with
      | `Error -> `Error
      | `Success (e2, pos)-> `Success (Comparision (c_op, e1, e2), pos)

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
  | `Success (ast, _) -> 
      print_expr_levels ast 0

let parse_and_print_comparision text =
  match comparision text 0 with
  | `Error -> Printf.printf "Error parsing comporission\n"
  | `Success (Comparision (c_op, left, right), _) -> 
    Printf.printf "Comporision %s\n"
    ( match (c_op) with
    | Equal-> "="
    | Less -> "<"
    | Greater -> ">"
    | Not_equal -> "<>"
    | Less_or_equal -> "<="
    | Greater_or_equal -> ">="
    );
    print_expr_levels left 1;
    print_expr_levels right 1

let read_file_as_string filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* example *)
let () =
  let input = read_file_as_string "test/test_input.txt" in
  parse_and_print input

  (* outside parser calling inside parsers of assignment, while or if 
     if any of them is true than call outside parser from current inside position
     else try another inside parser from starting position
    *)

(*comparision examples *)
(* let() =
  let input = read_file_as_string "test/test_comporision1_input" in
    parse_and_print_comparision input *)
(* let() =
  let input = read_file_as_string "test/test_comporision2_input" in
    parse_and_print_comparision input *)