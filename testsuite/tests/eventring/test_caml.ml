(* TEST *)
open Eventring

let major = ref 0
let minor = ref 0
let compact = ref 0
let majors = ref 0
let minors = ref 0
let compacts = ref 0

let got_start = ref false

let lifecycle ts lifecycle_event data =
    match lifecycle_event with
    | EV_START ->
        begin
            assert(match data with
            | Some(pid) -> true
            | None -> false);
            got_start := true
        end
    | _ -> ()

let runtime_begin ts phase =
    match phase with
    | EV_MAJOR ->
        begin
            assert(!major == 0);
            major := 1
        end
    | EV_MINOR ->
        begin
            assert(!minor == 0);
            minor := 1
        end
    | EV_COMPACT_MAIN ->
        begin
            assert(!compact == 0);
            compact := 1
        end
    | _ -> ()

let runtime_end ts phase =
    match phase with
    | EV_MAJOR ->
        begin
            assert(!major == 1);
            major := 0;
            incr majors
        end
    | EV_MINOR ->
        begin
            assert(!minor == 1);
            minor := 0;
            incr minors
        end;
    | EV_COMPACT_MAIN ->
        begin
            assert(!compact == 1);
            compact := 0;
            incr compacts
        end
    | _ -> ()

let () =
    start ();
    let cursor = create_cursor None in
    for a = 0 to 2 do
        ignore(Sys.opaque_identity(ref 42));
        Gc.compact ()
    done;
    let callbacks = { 
        ev_runtime_begin = Some(runtime_begin);
        ev_runtime_end = Some(runtime_end);
        ev_runtime_counter = None;
        ev_alloc = None;
        ev_lifecycle = Some(lifecycle);
        ev_lost_events = None
    } in 
    ignore(read_poll cursor callbacks (Some 1000));
    assert(!got_start);
    Printf.printf "minors: %d, majors: %d, compact: %d\n" !minors !majors !compacts