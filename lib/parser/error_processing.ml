let error_processing filename msg pos = 
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

  let read_file filename =
    let ic = open_in filename in
    let n = in_channel_length ic in
    let s = really_input_string ic n in
    close_in ic;
    s
  in

  let input = read_file filename in
  let (line_number, line, line_pos) = find_line input pos in
  (*
  Printf.printf "Error in line %d: %s:\n %s, position is %d \n" line_number msg line line_pos
  *)

  let indentation = String.make (line_pos) ' ' in
  Printf.printf "Error in line %d: %s:\n %s \n%s ^\n" line_number msg line indentation
