type ariphm_oper = Plus | Minus | Multiply | Divide

type ident = Ident of string * int (*int contains pos*)

type expr = 
  | Const of string
  | Var of ident
  | Binop of ariphm_oper * expr * expr

type comp_oper = 
  | Less
  | Greater
  | Less_or_equal
  | Greater_or_equal
  | Equal
  | Not_equal 

type comparision = Comparision of comp_oper * expr * expr

type statements = 
  | Assignment_and_tail of (ident * expr) * statements
  (*next 2 lines: int conatains start_pos*)
  | While_Do_Done_and_tail of (comparision * statements * int) * statements 
  | If_Then_Else_Fi_and_tail of (comparision * statements * statements * int) * statements
  (* string contains name, list -- args, expr is return expr *)
  | Function_and_tail of (string * ident list * statements) * statements
  | Return of expr * statements
  | Nothing