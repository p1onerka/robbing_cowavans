type ariphm_oper = Plus | Minus | Multiply | Divide

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

type ident = Ident of string

type statements = 
  | Assignment_and_tail of (ident * expr) * statements
  | While_Do_Done_and_tail of (comparision * statements) * statements
  | If_Then_Else_Fi_and_tail of (comparision * statements * statements) * statements
  | Nothing

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
  else if pos < find_len text && text.[pos] = '-' then
    match term text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> expr_tail (Binop (Minus, left, right)) text pos
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
  else if pos < find_len text && text.[pos] = '/' then
    match factor text (pos + 1) with
    | `Error -> `Error
    | `Success (right, pos) -> term_tail (Binop (Divide, left, right)) text pos
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
(* (Ksenia): "<" has three combinations so it is moved to outer function.
   note: it would prob be more beautiful to move ">" out too*)
let comp_oper text pos =
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

(* (Ksenia): take first expr, try to find comp oper, 
   combine it with second expr to form comparison *)
let comparision text pos =
  match expr text pos with 
  | `Error -> `Error
  | `Success (e1, pos) ->
    match comp_oper text pos with
    | `Error -> `Error
    | `Success (c_op, pos) -> 
      match expr text pos with
      | `Error -> `Error
      | `Success (e2, pos)-> `Success (Comparision (c_op, e1, e2), pos)

type end_marker = EOF | Word of string

(* wdd = while-do-done, itef = if-then-else-fi *)
(* (Ksenia): defines kind of statement by starting keyword 
   and calls corresponding func *)
let rec statements text pos end_marker =
  if pos >= find_len text && end_marker == EOF then `Success (Nothing, pos)
  else match ident_or_keyword text pos with
    | `Error -> `Error
    | `Success (id_or_kw, pos) ->
      match Word id_or_kw with
      | em when em = end_marker -> `Success (Nothing, pos)
      | Word "while" -> wdd_and_tail text pos end_marker
      | Word "if" -> itef_and_tail text pos end_marker
      | Word id -> 
        if (is_keyword id) then `Error
        else assignment_and_tail text pos (Ident id) end_marker
      | EOF -> `Error (* unreacheable *) 
       
(* (Ksenia): second version, wanna save it until im sure it is useless :)
and parse_assignment text pos ident prev_end_marker =
  let pos = ws text pos in
  if pos < find_len text && text.[pos] = ':' && pos + 1 < find_len text && text.[pos + 1] = '=' then
    let pos = ws text (pos + 2) in
    match expr text pos with
    | `Error -> `Error
    | `Success (e, pos) ->
        let pos = ws text pos in
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
let pos = ws text pos in
if pos + 1 < find_len text && text.[pos] = ':' && text.[pos + 1] = '=' then
  let pos = ws text (pos + 2) in
  match expr text pos with
  | `Error -> `Error
  | `Success (exp, pos) ->
    let pos = ws text pos in
    if pos < find_len text && text.[pos] = ';' then
      let pos = ws text (pos + 1) in
      match statements text pos prev_end_marker with
      | `Error -> `Error
      | `Success (st, pos) ->
        `Success (Assignment_and_tail ((ident, exp), st), pos)
    else `Error
else `Error


(* (Ksenia): forms a statement out of first found comparison 
   and given start/end marker to define the statement. 
   Additionaly forms tree of nested statements *)
and comp_and_statements text pos statements_start_word statements_end_marker = (*common part of wdd & itef*)
  match comparision text pos with
  | `Error -> `Error
  | `Success (comp_tree, pos) ->
    (match ident_or_keyword text pos with
    | `Success (ssw, pos) when ssw = statements_start_word ->
      (match statements text pos statements_end_marker with
      | `Error -> `Error
      | `Success (st, pos)-> `Success (comp_tree, st, pos))
    | _ -> `Error)

and wdd_and_tail text pos prev_end_marker = 
  match comp_and_statements text pos "do" (Word "done") with
  | `Error -> `Error
  | `Success (comp_tree, st, pos)->
    match statements text pos prev_end_marker  with
    | `Error -> `Error
    | `Success (tail, pos) -> 
      `Success (While_Do_Done_and_tail ((comp_tree, st), tail), pos)

and itef_and_tail text pos prev_end_marker = 
  match comp_and_statements text pos "then" (Word "else") with
  | `Error -> `Error
  | `Success (comp_tree, st1, pos)-> 
    (match statements text pos (Word "fi") with
    | `Error -> `Error
    | `Success (st2, pos)->
      (match statements text pos prev_end_marker  with
      | `Error -> `Error
      | `Success (tail, pos) -> 
        `Success (If_Then_Else_Fi_and_tail ((comp_tree, st1, st2), tail), pos)))

let read_file_as_string filename =
  let ic = open_in filename in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let rec print_expr_levels expr level =
  match expr with
  | Const n -> Printf.printf "%sConst %d\n" (String.make (level * 2) ' ') n
  | Var v -> Printf.printf "%sVar %s\n" (String.make (level * 2) ' ') v
  | Binop (op, left, right) ->
      Printf.printf "%sBinop %s\n" (String.make (level * 2) ' ') 
        (match op with Plus -> "+" | Minus -> "-" | Multiply -> "*" | Divide -> "/");
      print_expr_levels left (level + 1);
      print_expr_levels right (level + 1)

let parse_and_print text =
  match expr text 0 with
  | `Error -> Printf.printf "Error parsing expression\n"
  | `Success (ast, _) -> 
      print_expr_levels ast 0

let print_comporision_levels comparision level =
  let Comparision (c_op, left, right) = comparision in
  Printf.printf "%sComporision %s\n" (String.make (level * 2) ' ')
  ( match (c_op) with
  | Equal-> "="
  | Less -> "<"
  | Greater -> ">"
  | Not_equal -> "<>"
  | Less_or_equal -> "<="
  | Greater_or_equal -> ">="
  );
  print_expr_levels left (level + 1);
  print_expr_levels right (level + 1)

let parse_and_print_comparision text  =
  match comparision text 0 with
  | `Error -> Printf.printf "Error parsing comporission\n"
  | `Success (comparision, _) -> 
    print_comporision_levels comparision 0

let rec print_statements_levels statements level =
  match statements with
  | While_Do_Done_and_tail ((comp, st), tail) -> 
    Printf.printf "%sWhileDoDone_and_tail\n" (String.make (level * 2) ' ');
    print_comporision_levels comp (level + 1);
    print_statements_levels st (level + 1);
    print_statements_levels tail (level + 1)
  | If_Then_Else_Fi_and_tail ((comp, st1, st2), tail) ->
    Printf.printf "%sIfThenElseFi_and_tail\n" (String.make (level * 2) ' ');
    print_comporision_levels comp (level + 1);
    print_statements_levels st1 (level + 1);
    print_statements_levels st2 (level + 1);
    print_statements_levels tail (level + 1)
  | Assignment_and_tail ((Ident (ident), expr), tail) ->
    Printf.printf "%sAssignment_and tail\n" (String.make (level * 2) ' ');
    Printf.printf "%s%s\n" (String.make ((level + 1) * 2) ' ') ident;
    print_expr_levels expr (level + 1);
    print_statements_levels tail (level + 1)
  | Nothing -> Printf.printf "%s%s\n" (String.make (level * 2) ' ') "Nothing"

let program file_name =
  let input = read_file_as_string file_name in
    statements input 0 EOF

let parse_and_print_program file_name =
  match program file_name with
  | `Error -> Printf.printf "Error parsing programm\n"
  | `Success (statements,_) -> 
    print_statements_levels statements 0

(* example *)
(* let () =
  let input = read_file_as_string "test/test_input.txt" in
  parse_and_print input *)

  (* outside parser calling inside parsers of assignment, while or if 
     if any of them is true than call outside parser from current inside position
     else try another inside parser from starting position
    *)

(*comparision examples *)
(* let() =
  let input = read_file_as_string "test/test_comporision1_input.txt" in
    parse_and_print_comparision input *)
(* let() =
  let input = read_file_as_string "test/test_comporision2_input.txt" in
    parse_and_print_comparision input *)

(* statements/program example *)
let () =
     parse_and_print_program "test/test_full_program_input.txt" 
