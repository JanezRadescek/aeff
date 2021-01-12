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

let print s = Format.printf "%s@." s

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

let run_comp state comp (id : int) :
  state
  * Ast.computation
  * Ast.condition
  * (Ast.operation * Ast.expression * int) list =
  Format.printf "run_comp@.";

  let ops = ref [] in

  let counter = ref (-1) in
  let exit_code = ref Ast.Ready in

  let rec run_comp_rec (state : state) (comp : Ast.computation) :
    state * Ast.computation =
    Format.printf "comp = %t\n@." (Ast.print_computation comp);
    print "press anything to continiue";
    if true then
      try
        let _ = read_int () in
        ()
      with Failure _ -> ()
    else ();

    (* If exit code_is done parent might be do and we still have some work to do. on the contrary we will triger waiting only when we realy have to stop
       the problem before was we could come to promise somewhere in recursion and not realize it and call on same computation again not reazing we are not doing steps *)
    if !counter < 1000 then (
      incr counter;
      match comp with
      | Ast.Return _ ->
        exit_code := Ast.Done;
        (state, comp)
      | Ast.Do (Ast.Return e, abs) ->
        let state', comp' = substitution state e abs in
        run_comp_rec state' comp'
      | Ast.Do (c, abs) -> (
          let state', comp' = run_comp_rec state c in
          match comp' with
          | Ast.Return _ -> run_comp_rec state' (Ast.Do (comp', abs))
          | _ -> (state', Ast.Do (comp', abs)) )
      | Ast.Match (e, abs) ->
        let state', comp = eval_match state e abs in
        run_comp_rec state' comp
      | Ast.Apply (e1, e2) ->
        let state', e1e2 = eval_function state e1 e2 in
        run_comp_rec state' e1e2
      | Ast.Out (op, e, c) ->
        ops := (op, e, id) :: !ops;
        run_comp_rec state c
      | Ast.In (op, e, c) -> (
          match c with
          | Ast.Return _ ->
            exit_code := Ast.Done;
            (state, c)
          | Ast.Out (op', e', c') ->
            run_comp_rec state (Ast.Out (op', e', Ast.In (op, e, c')))
          | Ast.Promise (op', abs', var', c') when op = op' ->
            let state', comp' = substitution state e abs' in
            run_comp_rec state' (Ast.Do (comp', (Ast.PVar var', c')))
          | Ast.Promise (op', abs', var', c') ->
            let state', c'' = run_comp_rec state c' in
            run_comp_rec state'
              (Ast.Promise (op', abs', var', Ast.In (op, e, c'')))
          | _ ->
            let state', c' = run_comp_rec state c in
            (*Here we can get promise op, but it is rare so its ok to wait for next run_comp*)
            (state', Ast.In (op, e, c')) )
      | Ast.Promise (op, abs, p, c) ->
        let state', comp' = run_comp_rec state c in
        (state', Ast.Promise (op, abs, p, comp'))
      | Ast.Await (e, abs) when !counter = 0 ->
        (* promise must have been fulfiled since we are first in line *)
        let state', comp' = substitution state e abs in
        run_comp_rec state' comp'
      | Ast.Await _ ->
        exit_code := Ast.Waiting;
        (state, comp) )
    else (state, comp)
  in

  let state', comp' = run_comp_rec state comp in
  print "run_comp1";
  (state', comp', !exit_code, !ops)

(* match comp' with
   | Ast.Return e ->
   (state', Ast.Return (eval_expression state' e), Ast.Done, !ops)
   | Ast.In _ -> (state', comp', Ast.Waiting, !ops)
   | Ast.Promise _ -> (state', comp', Ast.Waiting, !ops)
   | _ ->
   Format.printf "THIS SHOULD NOT HAPPEN = %t@."
    (Ast.print_computation comp');
   assert false *)

let run_thread (state : state) ((comp, id, condition) : Ast.thread) :
  state * Ast.thread * (Ast.operation * Ast.expression * int) list =
  print "run_thread";
  match condition with
  | Ast.Ready ->
    let state', comp', condition', ops = run_comp state comp id in
    (state', (comp', id, condition'), ops)
  | _ -> (state, (comp, id, condition), [])

let resolve_operations (threads : Ast.thread list) ops : Ast.thread list * bool
  =
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
  (List.map insert_interupts threads, List.length ops = 0)

let rec run_rec (states : state list) (threads : Ast.thread list) :
  state list * Ast.thread list =
  print "run 1";
  let fold' state thread (states, threads, ops) =
    let state', thread', ops' = run_thread state thread in
    (state' :: states, thread' :: threads, ops' @ ops)
  in
  let states', threads', ops =
    List.fold_right2 fold' states threads ([], [], [])
  in
  print "run 3";
  let threads'', done' = resolve_operations threads' ops in
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
