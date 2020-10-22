open Utils
module Ast = Core.Ast
module Interpreter = Core.Interpreter
module Loader = Core.Loader

let make_top_step = function
  | Interpreter.TopOut (op, expr, proc) ->
      Format.printf "↑ %t %t@." (Ast.Operation.print op)
        (Ast.print_expression expr);
      proc
  | Interpreter.Step proc -> proc

let rec run (state : Interpreter.state) proc =
  match Interpreter.top_steps state proc with
  | [] -> proc
  | steps ->
      let i = Random.int (List.length steps) in
      let _, top_step = List.nth steps i in
      let proc' = make_top_step top_step in
      run state proc'

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
  let config = parse_args_to_config () in
  try
    Random.self_init ();
    let state =
      if config.use_stdlib then
        Loader.load_source Loader.initial_state Loader.stdlib_source
      else Loader.initial_state
    in
    let state = List.fold_left Loader.load_file state config.filenames in
    let proc = run state.interpreter (Loader.make_process state) in
    Format.printf "The process has terminated in the configuration:@.%t@."
      (Ast.print_process proc)
  with Error.Error error ->
    Error.print error;
    exit 1

let _ = main ()
