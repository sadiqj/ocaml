(* TEST
include runtime_events
*)
open Runtime_events

let counters_tbl = Hashtbl.create 50

let runtime_counter _domain_id ts name value =
    Hashtbl.add counters_tbl name value

let () =
    start ();
    let cursor = create_cursor None in
    let callbacks = Callbacks.create ~runtime_counter ()
    in
    Gc.set { (Gc.get()) with Gc.minor_heap_size = 524288 };
    Gc.full_major ();
    ignore(read_poll cursor callbacks None);
    (* Test the minor heap size change we did earlier is there *)
    assert(Hashtbl.find_opt counters_tbl
            EV_C_FORCE_MINOR_SET_MINOR_HEAP_SIZE |> Option.is_some);
    (* Now all the major heap sizings *)
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MAJOR_HEAP_POOL_WORDS |> Option.is_some);
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MAJOR_HEAP_POOL_LIVE_WORDS |> Option.is_some);
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MAJOR_HEAP_POOL_FRAG_WORDS |> Option.is_some);
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MAJOR_HEAP_POOL_LIVE_BLOCKS |> Option.is_some);
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MAJOR_HEAP_LARGE_WORDS |> Option.is_some);
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MAJOR_HEAP_LARGE_BLOCKS |> Option.is_some);
    (* Finally the minor heap counters *)
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MINOR_HEAP_SIZE_WORDS |> Option.is_some);
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MINOR_ALLOCATED |> Option.is_some);
    assert(Hashtbl.find_opt counters_tbl
            EV_C_MINOR_PROMOTED |> Option.is_some)
