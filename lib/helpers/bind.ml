let (let*) x f = match x with
  | `Error _ as e -> e
  | `Success x -> f x

let (let**) (x, new_msg) f = match x with
  | `Success x -> f x
  | `Error (msg, a) as e ->
    match msg with
    | empt_msg when empt_msg = String.empty -> `Error (new_msg, a)
    | _ -> e