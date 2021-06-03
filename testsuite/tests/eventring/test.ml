(* TEST
   modules = "stubs.c"
*)

external get_event_counts : unit -> (int * int * int) = "get_event_counts"

let () =
    for a = 0 to 2 do
        ignore(Sys.opaque_identity(ref 42));
        Gc.compact ()
    done;
    let (minors, majors, compacts) = get_event_counts () in
    Printf.printf "minors: %d, majors: %d, compact: %d\n" minors majors compacts