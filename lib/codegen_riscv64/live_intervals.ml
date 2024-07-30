open Parser.Types
open Helpers.Bind

(*for debugging*)
(* let print_intervalsHeap h =
  IntervalMinStartHeap.iter (fun elt -> 
    Printf.printf "start: %d, finish: %d, " elt.start elt.finish;
    let Ident (id, _), tags = elt.ident_and_tags in Printf.printf "id: %s\ntags: " id; List.iter (fun tag -> Printf.printf "%s " tag ) tags; 
    Printf.printf "\n") h
let rec print_intervalsMSHeap_sorted h =
  match IntervalMinStartHeap.take h with
  | None -> ()
  | Some (h, x) ->  (let print elt = 
    Printf.printf "start: %d, finish: %d, " elt.start elt.finish;
    let Ident (id, _), tags = elt.ident_and_tags in Printf.printf "id: %s\ntags: " id; List.iter (fun tag -> Printf.printf "%s " tag ) tags; 
    Printf.printf "\n" in print x; print_intervalsMSHeap_sorted h)
        
let rec print_intervalsMFHeap_sorted h =
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
  let (occupied, allocated), increase_val = stack_memory_info, 24 in
    if occupied > allocated - 8 then
      (Printf.fprintf output_file "addi sp, sp, %d\n" (-increase_val);
      (occupied, allocated + increase_val))
    else (occupied, allocated)

let compose_live_intervals program =
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

    let rec analyze_expr live_intervals_billet expr tags =
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
            `Success live_intervals_billet
      | Const _ -> `Success live_intervals_billet
      | Binop (_, expr1, expr2) -> 
        let* live_intervals_billet = analyze_expr live_intervals_billet expr1 tags in
          let* live_intervals_billet = analyze_expr live_intervals_billet expr2 tags in
            `Success live_intervals_billet
    in

      let analyze_comp live_inetrvals_billet comp tags =
        let Comparision (_, expr1, expr2) = comp in
          let* live_inetrvals_billet = analyze_expr live_inetrvals_billet expr1 tags in
            let* live_inetrvals_billet = analyze_expr live_inetrvals_billet expr2 tags  in
              `Success live_inetrvals_billet
      in

      let analyze_assign_s_ident live_intervals_billet ident tags =
        let Ident (_, ident_pos) = ident in
        let (interval, live_intervals_billet) =
          match remove_interval (ident, tags) live_intervals_billet with
          | (None, l_i_b) -> 
            ({start = ident_pos; finish = ident_pos; ident_and_tags = (ident, tags)}, l_i_b)
          | (Some interval, l_i_b) -> (*after implementing dead code cleaner there'll be no reason to remove interval in this case  *)
            ({start = interval.start; finish = ident_pos;
              ident_and_tags = interval.ident_and_tags}, l_i_b)
        in
          IntervalIdHeap.add live_intervals_billet interval
      in

        let rec compose_live_intervals_billet ?(tags = []) live_inetrvals_billet statements =
          match statements with
          | Nothing -> `Success live_inetrvals_billet
          | While_Do_Done_and_tail ((comp, st, pos), tl) ->
            let* live_inetrvals_billet = analyze_comp live_inetrvals_billet comp tags in          
              let* live_inetrvals_billet = compose_live_intervals_billet
                ~tags:(List.append tags (string_of_int(pos)::[])) live_inetrvals_billet st
              in
                let* live_inetrvals_billet = compose_live_intervals_billet
                  ~tags:tags live_inetrvals_billet tl
                in
                  `Success live_inetrvals_billet
        | If_Then_Else_Fi_and_tail ((comp, st1, st2, pos), tl) ->
          let* live_inetrvals_billet = analyze_comp live_inetrvals_billet comp tags in          
              let* live_inetrvals_billet = compose_live_intervals_billet
                ~tags:(List.append tags ((string_of_int(pos) ^ "th")::[])) live_inetrvals_billet st1
              in
                let* live_inetrvals_billet = compose_live_intervals_billet
                  ~tags:(List.append tags ((string_of_int(pos) ^ "el") :: [])) live_inetrvals_billet st2
                in
                  let* live_inetrvals_billet = compose_live_intervals_billet
                    ~tags:tags live_inetrvals_billet tl
                  in
                    `Success live_inetrvals_billet
        | Assignment_and_tail ((ident, expr),tl) ->
          let* live_inetrvals_billet = analyze_expr live_inetrvals_billet expr tags in
            let live_inetrvals_billet = analyze_assign_s_ident live_inetrvals_billet ident tags in
              let* live_inetrvals_billet = compose_live_intervals_billet
                ~tags:tags live_inetrvals_billet tl
              in `Success live_inetrvals_billet
        in

          let* live_intervals_billet = compose_live_intervals_billet ~tags:[] IntervalIdHeap.empty program in
            let rec transfer live_intervals live_intervals_billet =
              match IntervalIdHeap.take live_intervals_billet with
                | None -> live_intervals
                | Some (live_intervals_billet, interval) ->
                  transfer (IntervalMinStartHeap.add live_intervals interval) live_intervals_billet
            in
              `Success (transfer IntervalMinStartHeap.empty live_intervals_billet)

let rec expire_old_intervals pos active0 free_regs vars protected depth stack_memory_info output_file =
  match IntervalMinFinishHeap.take active0 with
  | None -> (active0, free_regs, vars, protected, stack_memory_info)
  | Some (active, interval) -> 
    if interval.finish >= pos then (active0, free_regs, vars, protected, stack_memory_info)
      (*snd is Reg "fake reg" cause it is unused in varheap_eq*)
    else  match VarHeap.remove_one varheap_eq (fst interval.ident_and_tags, Reg "fake reg") vars with
      | Some (_, Reg r), vars ->
        let protected = let depth_diff =  List.length (snd interval.ident_and_tags) - depth in
          if depth_diff >= 0 then protected
          else let stack_memory_info = stack_memory_check stack_memory_info output_file in
            let offset = - (fst stack_memory_info + 8) in
              Printf.fprintf output_file "sd %s, %d(s0)\n" r offset;
              (r, offset, depth_diff)::protected
        in
          let free_regs = FStack.push r free_regs in
            expire_old_intervals pos active free_regs vars protected depth stack_memory_info output_file
      | _ -> failwith "file live_intervals.ml/fun expire_old_intervals" (*unreachable*)

(*does'nt add allocated reg to free_regs!!! *)
let rec spill_allocated untouchables active vars protected depth stack_memory_info output_file =
  match IntervalMinFinishHeap.remove_bottommost active with
  | None,_ -> failwith "there are not enough registers"
  | Some interval, active -> (match List.find_opt (fun a -> a = get_id interval) untouchables with
    | Some _ ->  let r, active, vars, free_regs, protected, stack_memory_info =
      spill_allocated untouchables active vars protected depth stack_memory_info output_file in
        (r, (IntervalMinFinishHeap.add active interval), vars, free_regs, protected, stack_memory_info)
    | None ->
  (*increase stack allocated memory if that's necesary*)
      let stack_memory_info = stack_memory_check stack_memory_info output_file in
        let var, vars = VarHeap.remove_one varheap_eq (fst interval.ident_and_tags, Reg "fake reg") vars in
          match var with
          | Some (ident, Reg r ) ->
            let offset = - (fst stack_memory_info + 8) in
              Printf.fprintf output_file "sd %s, %d(s0)\n" r (offset);
              let vars = VarHeap.add vars (ident, OnStack (offset, interval)) in
              let protected = let depth_diff =  List.length (snd interval.ident_and_tags) - depth in
                if depth_diff < 0 then (r, offset, depth_diff) :: protected else protected
              in
                let stack_memory_info = ((fst stack_memory_info) + 8, snd stack_memory_info) in
                  (r, active, vars, (FStack.create), protected, stack_memory_info)
          | _ -> failwith "file live_intervals.ml/fun spill allocated" (*unreachable*))

let rec get_free_reg ?(eoi_applied = false) untouchables pos free_regs active vars protected depth stack_memory_info output_file =
  match FStack.pop free_regs with
  | None ->
    if not eoi_applied then
      let active, free_regs, vars, protected, stack_memory_info =
        expire_old_intervals pos active free_regs vars protected depth stack_memory_info output_file
      in
        get_free_reg ~eoi_applied:true untouchables pos free_regs active vars protected depth stack_memory_info output_file
    else 
      spill_allocated untouchables active vars protected depth stack_memory_info output_file
  | Some (free_regs, r) -> (r, active, vars, free_regs, protected, stack_memory_info)

(* doesn't add to active!*)
let move_spilled_var_to_reg  ?(reg = None) untouchables pos offset interval active free_regs vars protected depth stack_memory_info output_file =
    let vars = VarHeap.delete_one varheap_eq (fst interval.ident_and_tags, Reg "fake reg") vars in
      let allocated_reg, active, vars, free_regs, protected, stack_memory_info = match reg with
        | None -> (*(match FStack.pop free_regs with
          | None -> spill_allocated ~untouchables:untouchables active vars protected depth stack_memory_info output_file
          | Some (free_regs, allocated_reg) -> 
            (allocated_reg, active, vars, free_regs, protected, stack_memory_info)) *)
            get_free_reg untouchables pos free_regs active vars protected depth stack_memory_info output_file
        | Some r -> (r, active, vars, free_regs, protected, stack_memory_info)
      in
        Printf.fprintf output_file "ld %s, %d(s0)\n" allocated_reg offset;
        let vars = VarHeap.add vars (fst interval.ident_and_tags, Reg allocated_reg) in
          (allocated_reg, active, vars, free_regs, protected, stack_memory_info)

let rec initially_to_reg_alloc untouchables pos live_intervals free_regs active vars protected depth  stack_memory_info output_file =
  match IntervalMinStartHeap.take live_intervals with
    | Some (live_intervals, interval) when interval.start < pos -> 
      initially_to_reg_alloc untouchables pos live_intervals free_regs active vars protected depth stack_memory_info output_file
    | Some (live_intervals, interval) when interval.start = pos ->
      let active, free_regs, vars, protected, stack_memory_info =
        expire_old_intervals pos active free_regs vars protected depth stack_memory_info output_file
      in
        let allocated_reg, active, vars, free_regs, protected, stack_memory_info = match FStack.pop free_regs with 
          | None -> spill_allocated untouchables active vars protected depth stack_memory_info output_file
          | Some (free_regs, allocated_reg) -> 
            (allocated_reg, active, vars, free_regs, protected, stack_memory_info)
        in
          let active = IntervalMinFinishHeap.add active interval in
          let vars = VarHeap.add vars (fst interval.ident_and_tags, Reg allocated_reg) in
            (allocated_reg, live_intervals, active, vars, free_regs, protected, stack_memory_info)
    | _ -> failwith "file live_intervals.ml/fun initially_reg_allocated" (*unreachable*)
        
