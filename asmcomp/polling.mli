val polls_unconditionally : future_funcnames:Set.Make(String).t -> Mach.instruction -> bool
val is_leaf_func_without_loops : Mach.instruction -> bool
val instrument_fundecl : future_funcnames:Set.Make(String).t -> Mach.fundecl -> Mach.fundecl
val requires_prologue_poll : future_funcnames:Set.Make(String).t -> Mach.instruction -> bool