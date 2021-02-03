open Utils
module Ast = Core.Ast
module Interpreter = Core.Interpreter
module Loader = Core.Loader

let print s = Format.printf "%s@." s

type config = {
  filenames : string list;
  load_stdlib : bool;
  fixed_random_seed : bool;
}

let parse_args_to_config () =
  let filenames = ref []
  and load_stdlib = ref true
  and fixed_random_seed = ref false in
  let usage = "Run AEff as '" ^ Sys.argv.(0) ^ " [filename.aeff] ...'"
  and anonymous filename = filenames := filename :: !filenames
  and options =
    Arg.align
      [
        ( "--no-stdlib",
          Arg.Clear load_stdlib,
          " Do not load the standard library" );
        ( "--fixed-random-seed",
          Arg.Set fixed_random_seed,
          " Do not initialize the random seed" );
      ]
  in
  Arg.parse options anonymous usage;
  {
    filenames = List.rev !filenames;
    load_stdlib = !load_stdlib;
    fixed_random_seed = !fixed_random_seed;
  }

let main () =
  print "main";
  let config = parse_args_to_config () in
  try
    if not config.fixed_random_seed then Random.self_init ();
    let state =
      if config.load_stdlib then
        Loader.load_source Loader.initial_state Loader.stdlib_source
      else Loader.initial_state
    in

    let state = List.fold_left Loader.load_file state config.filenames in

    let finished_conf =
      Interpreter.run state.interpreter state.top_computations
    in
    Format.printf "The program has terminated in the configuration:@.";
    List.iter Interpreter.print_conf finished_conf
  with Error.Error error ->
    Error.print error;
    exit 1

let _ = main ()
