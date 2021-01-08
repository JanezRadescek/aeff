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

let extend_variables (state : state) vars =
  List.fold_left
    (fun state (x, expr) ->
       { state with variables = Ast.VariableMap.add x expr state.variables })
    state vars

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

let rec match_pattern_with_expression state pat expr :
  (Ast.variable * Ast.expression) list =
  match pat with
  | Ast.PVar x -> [ (x, expr) ]
  | Ast.PAnnotated (pat, _) -> match_pattern_with_expression state pat expr
  | Ast.PAs (pat, x) ->
    let vars = match_pattern_with_expression state pat expr in
    (x, expr) :: vars
  | Ast.PTuple pats ->
    let exprs = eval_tuple state expr in
    List.fold_left2
      (fun vars pat expr ->
         let vars' = match_pattern_with_expression state pat expr in
         vars' @ vars)
      [] pats exprs
  | Ast.PVariant (label, pat) -> (
      match (pat, eval_variant state expr) with
      | None, (label', None) when label = label' -> []
      | Some pat, (label', Some expr) when label = label' ->
        match_pattern_with_expression state pat expr
      | _, _ -> raise PatternMismatch )
  | Ast.PConst c when Const.equal c (eval_const state expr) -> []
  | Ast.PNonbinding -> []
  | _ -> raise PatternMismatch

let substitution state (v : Ast.expression) ((x, m) : Ast.abstraction) :
  state * Ast.computation =
  let vars = match_pattern_with_expression state x v in
  let state' = extend_variables state vars in
  (state', m)

let rec eval_expression state expr : Ast.expression =
  match expr with
  | Ast.Var x -> eval_expression state (Ast.VariableMap.find x state.variables)
  | Ast.Const _ -> expr
  | Ast.Annotated (e, _a) -> eval_expression state e
  | Ast.Tuple _ ->
    Ast.Tuple (List.map (eval_expression state) (eval_tuple state expr))
  | Ast.Variant (lbl, Some e) ->
    Ast.Variant (lbl, Some (eval_expression state e))
  | Ast.Variant (lbl, None) -> Ast.Variant (lbl, None)
  | Ast.Lambda _ | Ast.RecLambda _ -> expr
  | Ast.Fulfill e -> Ast.Fulfill (eval_expression state e)
  | Ast.Reference e -> Ast.Fulfill (eval_expression state !e)

let rec eval_function state f arg : state * Ast.computation =
  match f with
  | Ast.Lambda abs ->
    let state', farg = substitution state arg abs in
    (state', farg)
  | Ast.RecLambda (f, (pat, comp)) as expr ->
    let vars = match_pattern_with_expression state pat arg in
    let vars' = (f, expr) :: vars in
    let state' = extend_variables state vars' in
    (state', comp)
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.variables with
      | Some e -> eval_function state e arg
      | None ->
        let f' = Ast.VariableMap.find x state.builtin_functions in
        let arg' = eval_expression state arg in
        (state, f' arg') )
  | Ast.Annotated (e, _ty) -> eval_function state e arg
  | expr ->
    Error.runtime "Function expected but got %t" (Ast.print_expression expr)

let rec eval_match state e abs =
  match abs with
  | [] -> assert false
  | x :: xs -> (
      try substitution state e x with PatternMismatch -> eval_match state e xs )

let run_comp state comp : state * Ast.computation * Ast.condition =
  print "run_comp";
  let rec run_comp_rec (state : state) (comp : Ast.computation) =
    match comp with
    | Ast.Return _ -> (state, comp)
    | Ast.Do (Ast.Return e, abs) ->
      let state', comp' = substitution state e abs in
      run_comp_rec state' comp'
    | Ast.Do (c, abs) ->
      let state', comp' = run_comp_rec state c in
      run_comp_rec state' (Ast.Do (comp', abs))
    | Ast.Match (e, abs) ->
      let state', comp = eval_match state e abs in
      run_comp_rec state' comp
    | Ast.Apply (e1, e2) ->
      let state', e1e2 = eval_function state e1 e2 in
      run_comp_rec state' e1e2
    | Ast.Out _ -> (state, comp)
    | Ast.In (op, e, c) -> (
        match c with
        | Ast.Return _ -> (state, c)
        | Ast.Out (op', e', c') ->
          run_comp_rec state (Ast.Out (op', e', Ast.In (op, e, c')))
        | Ast.Promise (op', abs', var', comp') when op = op' ->
          let state', comp'' = substitution state e abs' in
          run_comp_rec state' (Ast.Do (comp'', (Ast.PVar var', comp')))
        | Ast.Promise (op', abs', var', c') ->
          let state', c'' = run_comp_rec state c' in
          run_comp_rec state'
            (Ast.Promise (op', abs', var', Ast.In (op, e, c'')))
        | _ ->
          let state', comp' = run_comp_rec state c in
          (*Here we can get promise op ... *)
          run_comp_rec state' (Ast.In (op, e, comp')) )
    | Ast.Promise (op, abs, p, c) ->
      let state', comp' = run_comp_rec state c in
      (state', Ast.Promise (op, abs, p, comp'))
    | Ast.Await _ -> failwith "TODO await"
    (*(state, comp)   How do we know if we have expression yet or not?*)
  in
  let state', comp' = run_comp_rec state comp in
  match comp' with
  | Ast.Return e -> (state', Ast.Return (eval_expression state' e), Ast.Done)
  | Ast.Out _ -> (state', comp', Ast.Ready)
  | Ast.In _ -> (state', comp', Ast.Waiting)
  | Ast.Promise _ -> (state', comp', Ast.Waiting)
  | _ -> assert false

let run_thread (state : state) ((comp, id, condition) : Ast.thread) :
  state * Ast.thread =
  print "run_thread";
  match condition with
  | Ast.Ready ->
    let state', comp', condition' = run_comp state comp in
    (state', (comp', id, condition'))
  | _ -> (state, (comp, id, condition))

let resolve_operations (threads : Ast.thread list) : Ast.thread list * bool =
  print "resolve";
  let take_op thread (ops, threads) =
    match thread with
    | Ast.Out (op, e, comp), id, cond ->
      ((op, e, id) :: ops, (comp, id, cond) :: threads)
    | _ -> (ops, thread :: threads)
  in
  let ops, threads' = List.fold_right take_op threads ([], []) in
  let insert_interupts (thread : Ast.thread) =
    let comp, id, _cond = thread in
    let comp' =
      List.fold_left
        (fun comp (op, expr, id') ->
           if id = id' then comp else Ast.In (op, expr, comp))
        comp ops
    in
    (comp', id, Ast.Ready)
  in
  (List.map insert_interupts threads', List.length ops = 0)

let rec run_rec (states : state list) (threads : Ast.thread list) :
  state list * Ast.thread list =
  print "run 1";
  let fold' state thread (states, threads) =
    let state', thread' = run_thread state thread in
    (state' :: states, thread' :: threads)
  in
  let states', threads' = List.fold_right2 fold' states threads ([], []) in
  print "run 3";
  let threads'', done' = resolve_operations threads' in
  print "run 4";
  match done' with
  | true -> (states', threads'')
  | false -> run_rec states' threads''

let run (state : state) (comps : Ast.computation list) =
  print "run";
  let rec make n = if n = 0 then [] else state :: make (n - 1) in
  let states = make (List.length comps) in
  let i = ref 0 in
  let threads =
    List.map
      (fun c ->
         let id = !i in
         incr i;
         (c, id, Ast.Ready))
      comps
  in
  run_rec states threads

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
