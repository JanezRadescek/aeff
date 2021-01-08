open Utils
module Ast = Core.Ast
module Interpreter = Core.Interpreter
module Loader = Core.Loader

let print s = Format.printf "%s\n" s

type config = { filenames : string list; use_stdlib : bool }

let parse_args_to_config () =
  let filenames = ref [] and use_stdlib = ref true in
  let usage = "Run AEff as '" ^ Sys.argv.(0) ^ " [filename.aeff] ...'"
  and anonymous filename = filenames := filename :: !filenames
  and options =
    Arg.align
      [
        ( "--no-stdlib",
          Arg.Clear use_stdlib,
          " Do not load the standard library" );
      ]
  in
  Arg.parse options anonymous usage;
  { filenames = List.rev !filenames; use_stdlib = !use_stdlib }

let main () =
  print "main";
  let config = parse_args_to_config () in
  try
    Random.self_init ();
    let state =
      if config.use_stdlib then
        Loader.load_source Loader.initial_state Loader.stdlib_source
      else Loader.initial_state
    in
    let state = List.fold_left Loader.load_file state config.filenames in
    let _states, finished_threads =
      Interpreter.run state.interpreter state.top_computations
    in
    Format.printf "The process has terminated in the configuration:\n";
    Ast.print_threads finished_threads
  with Error.Error error ->
    Error.print error;
    exit 1

let _ = main ()
