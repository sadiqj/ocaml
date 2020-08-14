module IntArg =
  struct
    type t = int
    let compare (x:int) (y:int) =
      if x < y then -1
      else if x > y then 1
      else 0
  end

module IntSet = Set.Make(IntArg)

let add_poll_before (f : Mach.instruction) : Mach.instruction =
  let new_live = Reg.Set.union f.live (Reg.Set.of_seq (Array.to_seq f.arg)) in
  { desc = Iop(Ipoll);
    next = f;
    arg = Array.make 0 Reg.dummy;
    res = Array.make 0 Reg.dummy;
    dbg = f.dbg;
    live = new_live;
    available_before = f.available_before;
    available_across = f.available_across; }

let rec find_rec_handlers (f : Mach.instruction) =
  match f.desc with
  | Iifthenelse(_, i0, i1) ->
    let i0_rec_handlers = find_rec_handlers i0 in
    let i1_rec_handlers = find_rec_handlers i1 in
    let next_rec_handlers = find_rec_handlers f.next in
      IntSet.(union (union i0_rec_handlers i1_rec_handlers) next_rec_handlers)
  | Iswitch(_, cases) ->
    let case_rec_handlers = Array.fold_left (fun int_set case -> IntSet.union int_set (find_rec_handlers case)) IntSet.empty cases
      in IntSet.union case_rec_handlers (find_rec_handlers f.next)
  | Icatch(rec_flag, handlers, body) ->
    (match rec_flag with 
    | Recursive -> begin
      let rec_handlers = List.fold_left (fun int_set (id, handler) -> IntSet.(add id (union (find_rec_handlers handler) int_set))) IntSet.empty handlers in
      let body_rec_handlers = find_rec_handlers body in
        IntSet.(union (union body_rec_handlers rec_handlers) (find_rec_handlers f.next))
      end
    | Nonrecursive ->
    begin
      let non_rec_catch_handlers = List.fold_left (fun int_set (_, handler) -> IntSet.union int_set (find_rec_handlers handler)) IntSet.empty handlers in
        let body_rec_handlers = find_rec_handlers body in 
          IntSet.(union (union body_rec_handlers non_rec_catch_handlers) (find_rec_handlers f.next))
    end)
  | Itrywith(body, handler) ->
    let handler_rec_handler = find_rec_handlers handler in
    let body_rec_handlers = find_rec_handlers body in
      IntSet.(union (union body_rec_handlers handler_rec_handler) (find_rec_handlers f.next))
  | Iexit(_) | Iend | Ireturn | Iop(Itailcall_ind _) | Iop(Itailcall_imm _) | Iraise _ ->
    IntSet.empty
  | Iop(_) -> 
    find_rec_handlers f.next

let rec add_polls_to_exit (rec_handlers : IntSet.t) (f : Mach.instruction) =
  match f.desc with
  | Iifthenelse(test, i0, i1) ->
    { f with desc = Iifthenelse(test, add_polls_to_exit rec_handlers i0, add_polls_to_exit rec_handlers i1); next = add_polls_to_exit rec_handlers f.next }
  | Iswitch(index, cases) ->
    { f with desc = Iswitch(index, Array.map (add_polls_to_exit rec_handlers) cases); next = add_polls_to_exit rec_handlers f.next }
  | Icatch(rec_flag, handlers, body) ->
    { f with desc = Icatch(rec_flag, List.map (fun (idx, instrs) -> (idx, (add_polls_to_exit rec_handlers) instrs)) handlers, add_polls_to_exit rec_handlers body); next = add_polls_to_exit rec_handlers f.next }
  | Itrywith(body, handler) ->
    { f with desc = Itrywith(add_polls_to_exit rec_handlers body, add_polls_to_exit rec_handlers handler); next = add_polls_to_exit rec_handlers f.next }
  | Iexit(id) ->
    if IntSet.mem id rec_handlers then
    let new_f = add_poll_before f in
      { new_f with next = { f with next = add_polls_to_exit rec_handlers f.next } }
    else
      { f with Mach.next = add_polls_to_exit rec_handlers f.next }
  | Iend | Ireturn | Iop(Itailcall_ind _) | Iop(Itailcall_imm _) | Iraise _ ->
    f    
  | Iop(_) -> 
    { f with next = add_polls_to_exit rec_handlers f.next }
    
let funcdecl (i : Mach.fundecl): Mach.fundecl =
  let f = i.fun_body in
    let rec_handlers = find_rec_handlers f in
      { i with fun_body = add_polls_to_exit rec_handlers f }