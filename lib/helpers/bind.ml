let (let*) x f = match x with
  | `Error _ as e -> e
  | `Success x -> f x