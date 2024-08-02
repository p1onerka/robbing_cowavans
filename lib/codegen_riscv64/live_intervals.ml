open Parser.Types
open Helpers.Bind

(*for debugging*)
(* let print_intervalsHeap h =
  IntervalMinStartHeap.iter (fun elt -> 
    Printf.printf "start: %d, finish: %d, " elt.start elt.finish;
    let Ident (id, _), tags = elt.ident_and_tags in Printf.printf "id: %s\ntags: " id; List.iter (fun tag -> Printf.printf "%s " tag ) tags; 
    Printf.printf "\n") h *)
(* let rec print_intervalsMSHeap_sorted h =
  match IntervalMinStartHeap.take h with
  | None -> ()
  | Some (h, x) ->  (let print elt = 
    Printf.printf "start: %d, finish: %d, " elt.start elt.finish;
    let Ident (id, _), tags = elt.ident_and_tags in Printf.printf "id: %s\ntags: " id; List.iter (fun tag -> Printf.printf "%s " tag ) tags; 
    Printf.printf "\n" in print x; print_intervalsMSHeap_sorted h)  *)
       
(* let rec print_intervalsMFHeap_sorted h =
  match IntervalMinFinishHeap.take h with
  | None -> ()
  | Some (h, x) ->  (let print elt = 
    Printf.printf "start: %d, finish: %d, " elt.start elt.finish;
    let Ident (id, _), tags = elt.ident_and_tags in Printf.printf "id: %s\ntags: " id; List.iter (fun tag -> Printf.printf "%s " tag ) tags; 
    Printf.printf "\n" in print x; print_intervalsMFHeap_sorted h) *)

let varheap_eq v1 v2 = let Ident (id1,_), Ident (id2,_)  = fst v1, fst v2 in
  String.equal id1 id2
let get_id interval = let Ident (id, _) = fst interval.ident_and_tags in id
let get_tags interval = snd interval.ident_and_tags
let get_pos interval = let Ident (_, pos) = fst interval.ident_and_tags in pos

let stack_memory_check stack_memory_info output_file =
  let (occupied, allocated), increase_val = stack_memory_info, 16 in
    if occupied > allocated - 8 then
      (Printf.fprintf output_file "addi sp, sp, %d\n" (-increase_val);
      (occupied, allocated + increase_val))
    else (occupied, allocated)

(*doesn't work with global vars!*)
let compose_live_intervals_heaps_and_calls_list program defs_list =

  let find_func_def ident args defs_list =
    let Ident(id1, _) = ident in
        List.find_opt (fun def -> let Ident (id2,_), params_count = def in id1 = id2 && params_count = List.length args) defs_list
  in

  let remove_interval (ident,tags) live_intervals_billet = 
    let eq interval1 interval2 = 
      (*order matters*)
      let rec tags_comp tags1 tags2 =
        match (tags1, tags2) with
        | (_, []) -> true
        | (hd1::tl1, hd2::tl2) ->
          if String.equal hd1 hd2 then tags_comp tl1 tl2
          else false
        | _ -> false
      in
        String.equal (get_id interval1) (get_id interval2) && 
          tags_comp (get_tags interval1) (get_tags interval2)
    in
      IntervalIdHeap.remove_one eq {start = -1; finish = -1;
        ident_and_tags =(ident, tags)} live_intervals_billet
  in

    let rec analyze_expr live_intervals_billet expr tags defs_list =
      match expr with
      | Var ident -> let Ident (ident_id, ident_pos) = ident in 
        let* (interval, live_intervals_billet) =
          match remove_interval (ident, tags) live_intervals_billet with
          | (None, _) -> `Error ("can't find '" ^ ident_id ^ "' variable's definition", ident_pos)
          | (Some interval, live_intervals_billet)-> `Success (interval, live_intervals_billet)
        in
          let live_intervals_billet = IntervalIdHeap.insert {start = interval.start; finish = ident_pos;
            ident_and_tags = interval.ident_and_tags} live_intervals_billet
          in
            `Success (live_intervals_billet, [])
      | Const _ -> `Success (live_intervals_billet, [])
      | Binop (_, expr1, expr2) -> 
        let* live_intervals_billet, calls1 = analyze_expr live_intervals_billet expr1 tags defs_list in
          let* live_intervals_billet, calls2 = analyze_expr live_intervals_billet expr2 tags defs_list in
            `Success (live_intervals_billet, calls1 @ calls2)
      | Func_Call (ident, args) -> 
        (match find_func_def ident args defs_list with
        | None ->  let Ident (_, pos) = ident in `Error ("undefined function was called", pos)
        | Some def ->
          (let calls1 = (fst def :: []) in
            let* live_intervals_billet, calls2 = analyze_func_args args live_intervals_billet tags defs_list in
              `Success (live_intervals_billet, calls1 @ calls2)))

      and analyze_func_args  args live_intervals_billet tags defs_list = 
        match args with 
        | [] -> `Success (live_intervals_billet, []) 
        | hd::tl -> let* live_intervals_billet, calls1 = analyze_expr live_intervals_billet hd tags defs_list in 
          let* live_intervals_billet, calls = analyze_func_args tl live_intervals_billet tags defs_list in
            `Success (live_intervals_billet, calls1 @ calls)
      in

      let analyze_comp live_intervals_billet comp tags =
        let Comparision (_, expr1, expr2) = comp in
          let* live_intervals_billet, calls1 = analyze_expr live_intervals_billet expr1 tags defs_list in
            let* live_intervals_billet, calls2 = analyze_expr live_intervals_billet expr2 tags defs_list in
              `Success (live_intervals_billet, calls1 @ calls2)
      in

      let analyze_assign_s_ident live_intervals_billet ident tags =
        let Ident (_, ident_pos) = ident in
        let (interval, live_intervals_billet) =
          match remove_interval (ident, tags) live_intervals_billet with
          | (None, l_i_b) ->  
            ({start = ident_pos; finish = ident_pos; ident_and_tags = (ident, tags)}, l_i_b)
          | (Some interval, l_i_b) ->
            ({start = interval.start; finish = ident_pos;
              ident_and_tags = interval.ident_and_tags}, l_i_b)
        in
          IntervalIdHeap.add live_intervals_billet interval
      in

      let analyze_func_params params = 
        let live_intervals_billet = IntervalIdHeap.empty in
          let rec analyze_params params live_intervals_billet =
            match params with
            | [] -> live_intervals_billet
            | hd::tl ->
              let Ident (_, ident_pos) = hd in
                let live_intervals_billet = 
                  IntervalIdHeap.add live_intervals_billet {start = ident_pos; finish = ident_pos; ident_and_tags = (hd, [])}
                in
                  analyze_params tl live_intervals_billet

          in
            analyze_params params live_intervals_billet
      in
        let rec compose_live_intervals_billets ?(tags = []) billet statements defs_list =
          (* List.iter print_string tags; print_newline();print_ident_int_list defs_list; print_newline(); *)
          match statements with
          | Nothing -> `Success (billet, [], [])
          | While_Do_Done_and_tail ((comp, (st, do_defs_list), pos), tl) ->
            let* billet, calls1 = analyze_comp billet comp tags in          
              let* billet, live_intervals_billets1, calls2 = compose_live_intervals_billets
                ~tags:(List.append tags (string_of_int(pos)::[])) billet st (do_defs_list @ defs_list)
              in
                let* billet, live_intervals_billets, calls = compose_live_intervals_billets
                  ~tags:tags billet tl defs_list
                in
                  `Success (billet , live_intervals_billets1 @ live_intervals_billets, calls1 @ calls2 @ calls)
          | If_Then_Else_Fi_and_tail ((comp, (st1, then_defs_list), (st2, else_defs_list), pos), tl) ->
            let* billet, calls1 = analyze_comp billet comp tags in          
                let* billet, live_intervals_billets1, calls2 = compose_live_intervals_billets
                    ~tags:(List.append tags ((string_of_int(pos) ^ "th")::[])) billet st1 (then_defs_list @ defs_list)
                in
                  let* billet, live_intervals_billets2, calls3 = compose_live_intervals_billets
                    ~tags:(List.append tags ((string_of_int(pos) ^ "el") :: [])) billet st2 (else_defs_list @ defs_list)
                  in
                    let* billet, live_intervals_billets, calls = compose_live_intervals_billets
                      ~tags:tags billet tl defs_list
                    in
                      `Success (billet,
                      (live_intervals_billets1 @ live_intervals_billets2 @ live_intervals_billets),
                      (calls1 @ calls2 @ calls3 @ calls))
          | Assignment_and_tail ((ident, expr),tl) ->
              let* billet, calls1 = analyze_expr billet expr tags defs_list in
                let billet = analyze_assign_s_ident billet ident tags in
                    let* billet, live_interval_billets, calls = 
                      compose_live_intervals_billets ~tags:tags billet tl defs_list
                    in
                    `Success (billet, live_interval_billets, calls1 @ calls )
          | Function_and_tail ((_, params, (body, inner_defs_list)), tl) -> 
            let billet_func = analyze_func_params params in
              let* billet_func, live_intervals_billets1, calls1 = 
                compose_live_intervals_billets billet_func body (inner_defs_list @ defs_list)
              in
              let* billet, live_intervals_billets, calls = compose_live_intervals_billets
                ~tags:tags billet tl defs_list
              in
                `Success (billet, (billet_func::live_intervals_billets1) @ live_intervals_billets, calls1 @ calls)

          | Function_Call ((ident, args), tl) ->
            (match find_func_def ident args defs_list with
            | None ->  let Ident (_, pos) = ident in `Error ("undefined function was called", pos)
            | Some def -> (let calls1 = (fst def :: []) in 
              let* billet, calls2 =
                  analyze_func_args args billet tags defs_list
              in
                let* billet, live_interval_billets, calls = compose_live_intervals_billets ~tags:tags billet tl defs_list
                in
                  `Success (billet, live_interval_billets, calls1 @ calls2 @ calls)))

          | Return (expr, tl) ->
            let* billet, calls1 = analyze_expr billet expr tags defs_list in
              let* billet, live_interval_billets, calls = compose_live_intervals_billets ~tags:tags billet tl defs_list
              in
                `Success (billet, live_interval_billets, calls1 @ calls)

        in

          let* _, live_intervals_billets, calls = 
            compose_live_intervals_billets IntervalIdHeap.empty program ((Ident ("print_int", 0), 1)::defs_list)
          in
            let rec transfer live_intervals live_intervals_billet=
              match IntervalIdHeap.take live_intervals_billet with
                | None -> live_intervals
                | Some (live_intervals_billet, interval) ->
                  transfer (IntervalMinStartHeap.add live_intervals interval) live_intervals_billet
            in
              `Success (
                List.map (transfer IntervalMinStartHeap.empty) live_intervals_billets,
                calls
              )

let rec expire_old_intervals pos context output_file =
  match IntervalMinFinishHeap.take context.active with
  | None -> context
  | Some (active, interval) -> 
    if interval.finish >= pos then context
      (*snd is Reg "fake reg" cause it is unused in varheap_eq*)
    else  match VarHeap.remove_one varheap_eq (fst interval.ident_and_tags, Reg "fake reg") context.vars with
      | Some (_, Reg r), vars ->
        let protected, stack_memory_info =
         let depth_diff =  List.length (snd interval.ident_and_tags) - context.depth in
            if depth_diff >= 0 then context.protected, context.stack_memory_info
            else let stack_memory_info = stack_memory_check context.stack_memory_info output_file in
              let offset = - (fst stack_memory_info + 8) in
                Printf.fprintf output_file "sd %s, %d(s0)\n" r offset;
                 (r, offset, depth_diff)::context.protected, stack_memory_info
        in
          let free_regs = FStack.push r context.free_regs in
            let context = {
              active = active;
              vars = vars; 
              protected = protected;
              stack_memory_info = stack_memory_info;
              free_regs = free_regs;
              depth = context.depth
              } in
            expire_old_intervals pos context output_file
      | _ -> failwith "file live_intervals.ml/fun expire_old_intervals" (*unreachable*)

(*does'nt add allocated reg to free_regs!!! *)
let rec spill_allocated ?(ident_and_register = None) ?(untouchables = []) context output_file =
  let move interval ident r context =
    (*increase stack allocated memory if that's necesary*)
    let stack_memory_info = stack_memory_check context.stack_memory_info output_file in
    let offset = - (fst stack_memory_info + 8) in
      Printf.fprintf output_file "sd %s, %d(s0)\n" r (offset);
      let vars = VarHeap.add context.vars (ident, OnStack (offset, interval)) in
      let protected = 
        let depth_diff =  List.length (snd interval.ident_and_tags) - context.depth in
          if depth_diff < 0 then (r, offset, depth_diff) :: context.protected
          else context.protected
      in
        let stack_memory_info = ((fst stack_memory_info) + 8, snd stack_memory_info) in
            r, { context with vars = vars; protected = protected; stack_memory_info = stack_memory_info}
  in
    match ident_and_register with (*may be changed after implementing s regs*)
    |Some (Ident (id, pos), r) -> (
        match IntervalMinFinishHeap.remove_one (fun i k -> get_id i = get_id k)
          {start = -1; finish = Int.max_int; ident_and_tags = (Ident (id, pos), [])} context.active
        with
        | None, _  -> failwith "file live_intervals.ml/fun spill allocated / 1" (*unreachable*)
        | Some interval, active ->  move interval (Ident (id, pos)) r {context with active = active})
    | None -> (match IntervalMinFinishHeap.remove_bottommost context.active with
      | None,_ -> failwith "there are not enough registers"
      | Some interval, active -> (match List.find_opt (fun a -> a = get_id interval) untouchables with
        | Some _ ->  let r, context =
          spill_allocated ~untouchables:untouchables {context with active = active} output_file in
            r,  {context with active = (IntervalMinFinishHeap.add active interval)}
        | None ->
          (let var, vars = VarHeap.remove_one varheap_eq (fst interval.ident_and_tags, Reg "fake reg") context.vars in
            match var with
            | Some (ident, Reg r ) -> move interval ident r {context with vars = vars; active = active}
            | _ -> failwith "file live_intervals.ml/fun spill allocated / 2" (*unreachable*))))

let get_due_reg register context output_file =
  match FStack.find_opt (fun r -> r = register) context.free_regs with
  | Some _ -> {context with free_regs = FStack.filter (fun r -> r <> register) context.free_regs}
  | None ->
    match VarHeap.remove_one (fun a  b -> snd a = snd b) (Ident ("fake_id", -1), Reg register) context.vars with
    |None, _ ->  context
    | Some var, vars -> snd (spill_allocated ~ident_and_register:(Some(fst var, register)) {context with vars = vars} output_file)

let rec get_free_reg ?(eoi_applied = false) untouchables pos context output_file =
  match FStack.pop context.free_regs with
  | None ->
    if not eoi_applied then
      let context =
        expire_old_intervals pos context output_file
      in
        get_free_reg ~eoi_applied:true untouchables pos context output_file
    else 
      spill_allocated ~untouchables:untouchables context output_file
  | Some (free_regs, r) -> r, {context with free_regs = free_regs} 

(* doesn't add to active!*)
let move_spilled_var_to_reg  ?(reg = None) untouchables pos offset interval context output_file =
    let vars = VarHeap.delete_one varheap_eq (fst interval.ident_and_tags, Reg "fake reg") context.vars in
      let allocated_reg, context = match reg with
        | None -> 
            get_free_reg untouchables pos context output_file
        | Some r -> r, {context with vars = vars}
      in
        Printf.fprintf output_file "ld %s, %d(s0)\n" allocated_reg offset;
        let vars = VarHeap.add vars (fst interval.ident_and_tags, Reg allocated_reg) in
          allocated_reg, {context with vars = vars}

let rec initially_to_reg_alloc untouchables pos live_intervals context output_file =
  match IntervalMinStartHeap.take live_intervals with
    | Some (live_intervals, interval) when interval.start < pos -> 
      initially_to_reg_alloc untouchables pos live_intervals context output_file
    | Some (live_intervals, interval) when interval.start = pos ->
      let context =
        expire_old_intervals pos context output_file
      in
        let allocated_reg, context = match FStack.pop context.free_regs with 
          | None -> spill_allocated ~untouchables:untouchables context output_file
          | Some (free_regs, allocated_reg) -> 
            allocated_reg, {context with free_regs = free_regs}
        in
          let active = IntervalMinFinishHeap.add context.active interval in
          let vars = VarHeap.add context.vars (fst interval.ident_and_tags, Reg allocated_reg) in
            allocated_reg, live_intervals, {context with active = active; vars = vars} 
    | _ -> failwith "file live_intervals.ml/fun initially_reg_allocated" (*unreachable*)
