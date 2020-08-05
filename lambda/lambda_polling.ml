open Lambda

let add_poll_before lambda =
    Lsequence (Lprim(Ppoll, [], Debuginfo.Scoped_location.Loc_unknown), lambda)

let add_polls l = 
    map (function 
            | Lfunction f -> 
                Lfunction { f with body = add_poll_before f.body }
            | x -> x) l