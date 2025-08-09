(* TEST
 include runtime_events;
*)

(* Multi-domain compaction test - verifies data integrity across domains *)

let num_domains = 4
let data_size = 1000

let () =
  let domains = Array.init num_domains (fun _ ->
    Domain.spawn (fun () ->
      let data = Array.init data_size (fun i -> ref i) in
      Gc.compact ();
      Array.iteri (fun i r -> assert (!r = i)) data
    )
  ) in
  Array.iter Domain.join domains;
  print_endline "Multi-domain compaction test passed"
