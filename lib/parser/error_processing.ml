(* perform understandable error printing with pointer to error position *)

let error_processing program msg pos = 
  let find_line text position =
    let rec aux index line_number line_start =
      if index >= position then
        let line_end = try String.index_from text line_start '\n' with Not_found -> String.length text in
        let line = String.sub text line_start (line_end - line_start) in
        (line_number, line, position - line_start)
      else if text.[index] = '\n' then
        aux (index + 1) (line_number + 1) (index + 1)
      else
        aux (index + 1) line_number line_start
    in
    aux 0 1 0
  in

  let (line_number, line, line_pos) = find_line program pos in

  let indentation = String.make (line_pos) ' ' in
  Printf.printf "Error in line %d: %s:\n %s \n%s ^\n" line_number msg line indentation
