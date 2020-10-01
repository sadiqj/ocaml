let () =
  Random.self_init ();
  exit (Optmaindriver.main Sys.argv Format.err_formatter)
