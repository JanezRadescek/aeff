open Utils

type state = {
  variables : Ast.expression Ast.VariableMap.t;
  builtin_functions : (Ast.expression -> Ast.computation) Ast.VariableMap.t;
}

let initial_state =
  {
    variables = Ast.VariableMap.empty;
    builtin_functions = Ast.VariableMap.empty;
  }

exception PatternMismatch

let print s = Format.printf "%s\n" s

let intersection_compliment aa bb =
  ( List.filter (fun (a1, _a2) -> List.mem a1 bb) aa,
    List.filter (fun b -> not (List.mem_assoc b aa)) bb )

let run_comp state comp : state * Ast.process * Ast.condition =
  print "run_comp";
  match comp with
  | Ast.Return _ -> (state, Ast.Run comp, Ast.Done)
  | _ -> failwith "TODO run_comp\n"

let rec run_process state process : state * Ast.process * Ast.condition =
  match process with
  | Ast.Run c ->
      let state', c', cond = run_comp state c in
      (state', c', cond)
  | Ast.OutProc (op, e, p) ->
      let state', p', cond = run_process state p in
      (state', Ast.OutProc (op, e, p'), cond)
  | Ast.InProc (_op, _e, p) -> (
      match p with
      | Ast.OutProc (_op', _e', _p') -> failwith "TODO"
      | Ast.InProc (_op', _e', _p') -> failwith "TODO"
      | Ast.Run (Ast.Promise (_op', _abs, _var, _comp)) -> failwith "TODO"
      | Ast.Run c -> run_comp state c )

let run_thread (state : state) ((process, ops, condition) : Ast.thread) =
  match condition with
  | Ast.Ready ->
      let state', process', condition' = run_process state process in
      (state', (process', ops, condition'))
  | _ -> (state, (process, ops, condition))

let resolve_operations (threads : Ast.thread list) : Ast.thread list * bool =
  print "resolve";
  let take_op thread (ops, threads) =
    match thread with
    | Ast.OutProc (op, e, proc), ops', cond ->
        ((op, e) :: ops, (proc, ops', cond) :: threads)
    | (Ast.Run _ | Ast.InProc _), _, _ -> (ops, thread :: threads)
  in
  let op, threads' = List.fold_right take_op threads ([], []) in
  let insert_interupts thread threads =
    let proc, op', _cond = thread in
    let op_todo, op'' = intersection_compliment op op' in
    let proc' =
      List.fold_left
        (fun proc (op, expr) -> Ast.InProc (op, expr, proc))
        proc op_todo
    in
    let thread' = (proc', op'', Ast.Ready) in
    thread' :: threads
  in
  (List.fold_right insert_interupts threads' [], List.length op = 0)

let rec run (state : state) (threads : Ast.thread list) : Ast.thread list =
  print "run 1";
  let fold' thread (state, threads) =
    let state', thread' = run_thread state thread in
    (state', thread' :: threads)
  in
  print "run 2";
  let state', threads' = List.fold_right fold' threads (state, []) in
  print "run 3";
  let threads'', done' = resolve_operations threads' in
  print "run 4";
  match done' with true -> threads'' | false -> run state' threads''

let add_external_function x def state =
  {
    state with
    builtin_functions = Ast.VariableMap.add x def state.builtin_functions;
  }

let eval_top_let state x expr =
  { state with variables = Ast.VariableMap.add x expr state.variables }

(*let make_top_step = function
  | Interpreter.TopOut (op, expr, proc) ->
      Format.printf "↑ %t %t@." (Ast.Operation.print op)
        (Ast.print_expression expr);
      proc
  | Interpreter.Step proc -> proc *)

(*type computation_redex =
  | PromiseOut
  | InReturn
  | InOut
  | InPromise
  | InPromise'
  | Match
  | ApplyFun
  | DoReturn
  | DoOut
  | DoPromise
  | AwaitFulfill

  type computation_reduction =
  | PromiseCtx of computation_reduction
  | InCtx of computation_reduction
  | OutCtx of computation_reduction
  | DoCtx of computation_reduction
  | ComputationRedex of computation_redex

  type process_redex =
  | RunOut
  | ParallelOut1
  | ParallelOut2
  | InRun
  | InParallel
  | InOut
  | TopOut

  type process_reduction =
  | LeftCtx of process_reduction
  | RightCtx of process_reduction
  | InProcCtx of process_reduction
  | OutProcCtx of process_reduction
  | RunCtx of computation_reduction
  | ProcessRedex of process_redex

  let rec eval_tuple state = function
  | Ast.Tuple exprs -> exprs
  | Ast.Var x -> eval_tuple state (Ast.VariableMap.find x state.variables)
  | Ast.Annotated (e, _anno) -> eval_tuple state e
  | expr ->
      Error.runtime "Tuple expected but got %t" (Ast.print_expression expr)

  let rec eval_variant state = function
  | Ast.Variant (lbl, expr) -> (lbl, expr)
  | Ast.Var x -> eval_variant state (Ast.VariableMap.find x state.variables)
  | Ast.Annotated (e, _anno) -> eval_variant state e
  | expr ->
      Error.runtime "Variant expected but got %t" (Ast.print_expression expr)

  let rec eval_const state = function
  | Ast.Const c -> c
  | Ast.Var x -> eval_const state (Ast.VariableMap.find x state.variables)
  | Ast.Annotated (e, _anno) -> eval_const state e
  | expr ->
      Error.runtime "Const expected but got %t" (Ast.print_expression expr)

  let rec match_pattern_with_expression state pat expr =
  match pat with
  | Ast.PVar x -> Ast.VariableMap.singleton x expr
  | Ast.PAnnotated (pat, _) -> match_pattern_with_expression state pat expr
  | Ast.PAs (pat, x) ->
      let subst = match_pattern_with_expression state pat expr in
      Ast.VariableMap.add x expr subst
  | Ast.PTuple pats ->
      let exprs = eval_tuple state expr in
      List.fold_left2
        (fun subst pat expr ->
          let subst' = match_pattern_with_expression state pat expr in
          Ast.VariableMap.union (fun _ _ _ -> assert false) subst subst')
        Ast.VariableMap.empty pats exprs
  | Ast.PVariant (label, pat) -> (
      match (pat, eval_variant state expr) with
      | None, (label', None) when label = label' -> Ast.VariableMap.empty
      | Some pat, (label', Some expr) when label = label' ->
          match_pattern_with_expression state pat expr
      | _, _ -> raise PatternMismatch )
  | Ast.PConst c when Const.equal c (eval_const state expr) ->
      Ast.VariableMap.empty
  | Ast.PNonbinding -> Ast.VariableMap.empty
  | _ -> raise PatternMismatch

  let substitute subst comp =
  let subst = Ast.VariableMap.map (Ast.refresh_expression []) subst in
  Ast.substitute_computation subst comp

  let rec eval_function state = function
  | Ast.Lambda (pat, comp) ->
      fun arg ->
        let subst = match_pattern_with_expression state pat arg in
        substitute subst comp
  | Ast.RecLambda (f, (pat, comp)) as expr ->
      fun arg ->
        let subst =
          match_pattern_with_expression state pat arg
          |> Ast.VariableMap.add f expr
        in
        substitute subst comp
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.variables with
      | Some expr -> eval_function state expr
      | None -> Ast.VariableMap.find x state.builtin_functions )
  | Ast.Annotated (expr, _ty) -> eval_function state expr
  | expr ->
      Error.runtime "Function expected but got %t" (Ast.print_expression expr)

  let step_in_context step state redCtx ctx term =
  let terms' = step state term in
  List.map (fun (red, term') -> (redCtx red, ctx term')) terms'

  let rec step_computation state = function
  | Ast.Return _ -> []
  | Ast.Out (op, expr, comp) ->
      step_in_context step_computation state
        (fun red -> OutCtx red)
        (fun comp' -> Ast.Out (op, expr, comp'))
        comp
  | Ast.Promise (op, op_comp, p, comp) -> (
      let comps' =
        step_in_context step_computation state
          (fun red -> PromiseCtx red)
          (fun comp' -> Ast.Promise (op, op_comp, p, comp'))
          comp
      in
      match comp with
      | Ast.Out (op', expr', cont') ->
          ( ComputationRedex PromiseOut,
            Ast.Out (op', expr', Ast.Promise (op, op_comp, p, cont')) )
          :: comps'
      | _ -> comps' )
  | Ast.In (op, expr, comp) -> (
      let comps' =
        step_in_context step_computation state
          (fun red -> InCtx red)
          (fun comp' -> Ast.In (op, expr, comp'))
          comp
      in
      match comp with
      | Ast.Return expr ->
          (ComputationRedex InReturn, Ast.Return expr) :: comps'
      | Ast.Out (op', expr', cont') ->
          ( ComputationRedex InOut,
            Ast.Out (op', expr', Ast.In (op, expr, cont')) )
          :: comps'
      | Ast.Promise (op', (arg_pat, op_comp), p, comp) when op = op' ->
          let subst = match_pattern_with_expression state arg_pat expr in
          let y = Ast.Variable.fresh None in
          let comp' =
            Ast.Do
              ( substitute subst op_comp,
                ( Ast.PVar y,
                  Ast.Do
                    ( Ast.Return (Ast.Var y),
                      (Ast.PVar p, Ast.In (op, expr, comp)) ) ) )
          in
          (ComputationRedex InPromise, comp') :: comps'
      | Ast.Promise (op', op_comp, p, comp) ->
          ( ComputationRedex InPromise',
            Ast.Promise (op', op_comp, p, Ast.In (op, expr, comp)) )
          :: comps'
      | _ -> comps' )
  | Ast.Match (expr, cases) ->
      let rec find_case = function
        | (pat, comp) :: cases -> (
            match match_pattern_with_expression state pat expr with
            | subst -> [ (ComputationRedex Match, substitute subst comp) ]
            | exception PatternMismatch -> find_case cases )
        | [] -> []
      in
      find_case cases
  | Ast.Apply (expr1, expr2) ->
      let f = eval_function state expr1 in
      [ (ComputationRedex ApplyFun, f expr2) ]
  | Ast.Do (comp1, comp2) -> (
      let comps1' =
        step_in_context step_computation state
          (fun red -> DoCtx red)
          (fun comp1' -> Ast.Do (comp1', comp2))
          comp1
      in
      match comp1 with
      | Ast.Return expr ->
          let pat, comp2' = comp2 in
          let subst = match_pattern_with_expression state pat expr in
          (ComputationRedex DoReturn, substitute subst comp2') :: comps1'
      | Ast.Out (op, expr, comp1) ->
          (ComputationRedex DoOut, Ast.Out (op, expr, Ast.Do (comp1, comp2)))
          :: comps1'
      | Ast.Promise (op, op_comp, pat, comp1) ->
          ( ComputationRedex DoPromise,
            Ast.Promise (op, op_comp, pat, Ast.Do (comp1, comp2)) )
          :: comps1'
      | _ -> comps1' )
  | Ast.Await (expr, (pat, comp)) -> (
      match expr with
      | Ast.Fulfill expr ->
          let subst = match_pattern_with_expression state pat expr in
          [ (ComputationRedex AwaitFulfill, substitute subst comp) ]
      | _ -> [] )

  let rec step_process state = function
  | Ast.Run comp -> (
      let comps' =
        step_computation state comp
        |> List.map (fun (red, comp') -> (RunCtx red, Ast.Run comp'))
      in
      match comp with
      | Ast.Out (op, expr, comp') ->
          (ProcessRedex RunOut, Ast.OutProc (op, expr, Ast.Run comp')) :: comps'
      | _ -> comps' )
  | Ast.InProc (op, expr, proc) -> (
      let procs' =
        step_in_context step_process state
          (fun red -> InProcCtx red)
          (fun proc' -> Ast.InProc (op, expr, proc'))
          proc
      in
      match proc with
      | Ast.Run comp ->
          (ProcessRedex InRun, Ast.Run (Ast.In (op, expr, comp))) :: procs'
      | Ast.OutProc (op', expr', proc') ->
          ( ProcessRedex InOut,
            Ast.OutProc (op', expr', Ast.InProc (op, expr, proc')) )
          :: procs'
      | _ -> procs' )
  | Ast.OutProc (op, expr, proc) ->
      step_in_context step_process state
        (fun red -> OutProcCtx red)
        (fun proc' -> Ast.OutProc (op, expr, proc'))
        proc

  let incoming_operation proc op expr = Ast.InProc (op, expr, proc)





  type top_step =
  | TopOut of Ast.operation * Ast.expression * Ast.process
  | Step of Ast.process

  let top_steps state proc =
  let steps =
    step_process state proc |> List.map (fun (red, proc) -> (red, Step proc))
  in
  match proc with
  | Ast.OutProc (op, expr, proc) ->
      (ProcessRedex TopOut, TopOut (op, expr, proc)) :: steps
  | _ -> steps
*)
