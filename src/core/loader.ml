open Utils

let parse_commands lexbuf =
  try Parser.commands Lexer.token lexbuf with
  | Parser.Error ->
      Error.syntax
        ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf))
        "parser error"
  | Failure failmsg when failmsg = "lexing: empty token" ->
      Error.syntax
        ~loc:(Location.of_lexeme (Lexing.lexeme_start_p lexbuf))
        "unrecognised symbol."

type state = {
  desugarer : Desugarer.state;
  interpreter : Interpreter.state;
  typechecker : Typechecker.state;
  top_computations : Ast.thread list;
}

let initial_state =
  let load_function state (x, ty_sch, def) =
    let desugarer_state', x' =
      Desugarer.add_external_variable x state.desugarer
    in
    let interpreter_state' =
      Interpreter.add_external_function x' def state.interpreter
    in
    let typechecker_state' =
      Typechecker.add_external_function x' ty_sch state.typechecker
    in
    {
      state with
      desugarer = desugarer_state';
      interpreter = interpreter_state';
      typechecker = typechecker_state';
    }
  in
  {
    desugarer = Desugarer.initial_state;
    interpreter = Interpreter.initial_state;
    typechecker = Typechecker.initial_state;
    top_computations = [];
  }
  |> fun state -> List.fold load_function state BuiltIn.functions

let make_thread comp : Ast.thread =
  let rec find_op_comp comp : Ast.operation list =
    match comp with
    | Ast.Return e -> find_op_expression e
    | _ -> failwith "TODO"
  and find_op_expression _expr = failwith "TODO" in

  (Ast.Run comp, find_op_comp comp, Ast.Ready)

let execute_command state = function
  | Ast.TyDef ty_defs ->
      let typechecker_state' =
        Typechecker.add_type_definitions state.typechecker ty_defs
      in
      { state with typechecker = typechecker_state' }
  | Ast.TopLet (x, ty_sch, expr) ->
      let interpreter_state' =
        Interpreter.eval_top_let state.interpreter x expr
      in
      let typechecker_state' =
        Typechecker.add_top_definition state.typechecker x ty_sch expr
      in
      {
        state with
        interpreter = interpreter_state';
        typechecker = typechecker_state';
      }
  | Ast.TopDo comp ->
      let _ = Typechecker.infer_top_computation state.typechecker comp in
      let thread = make_thread comp in
      { state with top_computations = thread :: state.top_computations }
  | Ast.Operation (op, ty) ->
      let typechecker_state' =
        Typechecker.add_operation state.typechecker op ty
      in
      { state with typechecker = typechecker_state' }

let load_commands state cmds =
  let desugarer_state', cmds' =
    List.fold_map Desugarer.desugar_command state.desugarer cmds
  in
  let state' = { state with desugarer = desugarer_state' } in
  List.fold_left execute_command state' cmds'

let load_source state source =
  let lexbuf = Lexing.from_string source in
  let cmds = parse_commands lexbuf in
  load_commands state cmds

let load_file state source =
  let cmds = Lexer.read_file parse_commands source in
  load_commands state cmds

let parse_payload state op input =
  let lexbuf = Lexing.from_string input in
  let term = Parser.payload Lexer.token lexbuf in
  let expr' = Desugarer.desugar_pure_expression state.desugarer term in
  ignore (Typechecker.check_payload state.typechecker op expr');
  expr'

(** The module Stdlib_aeff is automatically generated from stdlib.aeff. Check the dune file for details. *)
let stdlib_source = Stdlib_aeff.contents
