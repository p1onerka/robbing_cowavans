type ariphm_oper = Plus | Minus | Multiply | Divide

type ident = Ident of string * int (*int contains pos*)

type expr = 
  | Const of string
  | Var of ident
  | Binop of ariphm_oper * expr * expr
  | Func_Call of ident * expr list (* expr here is Var *)

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
  | While_Do_Done_and_tail of (comparision * (statements * (ident*int) list) * int) * statements 
  | If_Then_Else_Fi_and_tail of (comparision * (statements * (ident*int) list) * (statements * (ident*int) list) * int) * statements

  (* string contains name, list -- args, expr is return expr *)
  | Function_and_tail of (ident * ident list * (statements * (ident*int) list)) * statements
  | Return of expr * statements
  | Function_Call of (ident * expr list) * statements
  | Nothing


type state = int (* maybe need to change it somewhere when we make it work *)

type var_live_interval = {start : int; finish : int; ident_and_tags : ident * string list }

type var_s_placement =
  | Reg of string
  | OnStack of int * var_live_interval


module IntervalMinFinishHeap = CCHeap.Make(
    struct type t = var_live_interval
    let leq x y = x.finish <= y.finish  end );;

module IntervalMinStartHeap = CCHeap.Make(
    struct type t = var_live_interval
    let leq x y = x.start <= y.start  end );;

module IntervalIdHeap = CCHeap.Make(
  struct type t = var_live_interval
  let leq x y =
    let Ident (x_id,_), _ = x.ident_and_tags in
    let Ident (y_id,_), _ = y.ident_and_tags in
      x_id <= y_id
  end);;

module VarHeap = CCHeap.Make(
    struct type t = ident * var_s_placement
    let leq x y =
      let Ident (x_id,_) = fst x in
      let Ident (y_id,_) = fst y in
        x_id <= y_id
    end);;

    module type FStack_i = sig
      type 'a fstack
      val create : 'a fstack
      val is_empty : 'a fstack -> bool
      val push : 'a -> 'a fstack -> 'a fstack
      val pop : 'a fstack -> ('a fstack * 'a) option
      val peek : 'a fstack -> 'a option
      val add_list: 'a fstack -> 'a list -> 'a fstack
    
      val filter: ('a -> bool) -> 'a fstack -> 'a fstack
      val iter: ('a -> unit) -> 'a fstack -> unit
      val find_opt : ('a -> bool) -> 'a fstack -> 'a option
    end
    
    module FStack : FStack_i = struct
     type 'a fstack = 'a list
      let create = []
      let is_empty = function 
        | [] -> true
        | _ -> false
      let push el = function
        | [] ->  el::[]
        | list -> el::list
      let pop = function
        | [] -> None
        | hd::tl -> Some (tl, hd)
      
      let peek = function
        |[] -> None
        | hd::_ -> Some hd
      
      let add_list list = function
      | [] -> list
      | l -> List.append l list
      let iter f = function
      | [] -> ()
      | l -> List.iter f l
    
      let filter cond = function
      | [] -> []
      | l -> List.filter cond l
    
      let find_opt cond = function
      | [] -> None
      | l -> List.find_opt cond l
    end
    
    (*stack_memory_info is occupied stack memory size and allocated stack memory size *)
    (*depth = last do/then/else block's (for which this expr is inner) depth*)
    (*protected = reg, offset, depth_diff: list for return due vars to their regs after loop*)
    type context = {
      vars : VarHeap.t;
      active : IntervalMinFinishHeap.t;
      free_regs : string FStack.fstack;
      protected : (string*int*int) list;
      depth : int;
      stack_memory_info : int*int;
    }
    