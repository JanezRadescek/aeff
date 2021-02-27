open Utils

let debugg = false

exception PatternMismatch

let print s = Format.printf "%s@." s

type result =
  | Done of Ast.expression
  | Await of Ast.computation
  | Ready of Ast.computation

let print_result = function
  | Done e -> Format.printf "Done expr = %t@." (Ast.print_expression e)
  | Ready c -> Format.printf "Ready comp = %t@." (Ast.print_computation c)
  | Await c -> Format.printf "Await comp = %t@." (Ast.print_computation c)

type state = {
  toplet : Ast.expression Ast.VariableMap.t;
  builtin_functions : (Ast.expression -> Ast.computation) Ast.VariableMap.t;
}

let initial_state =
  { toplet = Ast.VariableMap.empty; builtin_functions = Ast.VariableMap.empty }

type conf = {
  counter : int;
  id : int;
  ops : (Ast.operation * Ast.expression * int) list;
  res : result;
}

let print_conf conf =
  Format.printf "Conf\n  id = %d;@." conf.id;
  Format.printf
    ( match conf.res with
    | Done _ -> "Done"
    | Await _ -> "Await"
    | Ready _ -> "Ready" );
  Format.printf "\nres = %t@."
    ( match conf.res with
    | Done e -> Ast.print_expression e
    | Await c | Ready c -> Ast.print_computation c )

let rec match_pattern_with_value (pat : Ast.pattern) (e : Ast.expression) :
    (Ast.variable * Ast.expression) list =
  match pat with
  | Ast.PVar x -> [ (x, e) ]
  | Ast.PAnnotated (pat, _) -> match_pattern_with_value pat e
  | Ast.PAs (pat, x) ->
      let vars = match_pattern_with_value pat e in
      (x, e) :: vars
  | Ast.PTuple pats -> (
      match e with
      | Tuple es ->
          List.fold_left2
            (fun vars pat e ->
              let vars' = match_pattern_with_value pat e in
              vars' @ vars)
            [] pats es
      | _ -> raise PatternMismatch )
  | Ast.PVariant (label, pat') -> (
      match e with
      | Variant (label', e') when label = label' -> (
          match (pat', e') with
          | None, None -> []
          | Some pat'', Some e'' -> match_pattern_with_value pat'' e''
          | _ -> raise PatternMismatch )
      | _ -> raise PatternMismatch )
  | Ast.PConst c -> (
      match e with
      | Const c' when Const.equal c c' -> []
      | _ -> raise PatternMismatch )
  | Ast.PNonbinding -> []

let substitution (e : Ast.expression) ((x, m) : Ast.abstraction) :
    Ast.computation =
  let vars = match_pattern_with_value x e in
  let subst = Ast.VariableMap.empty in
  let subst' =
    List.fold_left (fun sub (x, v) -> Ast.VariableMap.add x v sub) subst vars
  in
  let subst'' = Ast.VariableMap.map (Ast.refresh_expression []) subst' in
  Ast.substitute_computation subst'' m

let rec eval_expression state (expr : Ast.expression) : Ast.expression =
  match expr with
  | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.toplet with
      | None -> expr
      | Some e -> eval_expression state e )
  | Ast.Annotated (e, _a) -> eval_expression state e
  | e -> e

let rec eval_match (e : Ast.expression) abs : Ast.computation =
  match abs with
  | [] -> assert false
  | x :: xs -> (
      try substitution e x with PatternMismatch -> eval_match e xs )

let eval_fulfill (e : Ast.expression) =
  match e with
  | Ast.Var _x -> None
  | Ast.Fulfill e -> Some e
  | _ -> assert false

let big_step state (conf : conf) : conf =
  let rec small_steps (conf_small : conf) : conf =
    (* print_state conf_small.vars; *)
    (* Format.printf "comp = %t\n@." (Ast.print_computation conf_small.res); *)
    if debugg then (
      print_conf conf_small;
      Format.printf "count = %i@." conf_small.counter;
      print "press enter to do SMALL step";
      try
        let _ = read_int () in
        ()
      with Failure _ -> () );

    if conf_small.counter < 1000 then
      let cs = { conf_small with counter = conf_small.counter + 1 } in
      match cs.res with
      | Done _ -> cs
      | Await _ -> cs
      | Ready comp -> (
          match comp with
          | Ast.Return e -> { cs with res = Done (eval_expression state e) }
          | Ast.Do (c, abs) -> (
              match c with
              | Ast.Return e ->
                  let comp' = substitution e abs in
                  small_steps { cs with res = Ready comp' }
              | Ast.Promise (k, op, abs', p, c') ->
                  small_steps
                    {
                      cs with
                      res =
                        Ready (Ast.Promise (k, op, abs', p, Ast.Do (c', abs)));
                    }
              | _ -> (
                  let cs' = small_steps { cs with res = Ready c } in

                  match cs'.res with
                  | Done e ->
                      let c' = substitution e abs in

                      small_steps { cs' with res = Ready c' }
                  | Await c' -> (
                      match c' with
                      | Ast.Promise _ ->
                          small_steps
                            { cs' with res = Ready (Ast.Do (c', abs)) }
                      | _ -> { cs' with res = Await (Ast.Do (c', abs)) } )
                  | Ready c' -> (
                      match c' with
                      | Ast.Promise _ ->
                          small_steps
                            { cs' with res = Ready (Ast.Do (c', abs)) }
                      | _ -> { cs' with res = Ready (Ast.Do (c', abs)) } ) ) )
          | Ast.Match (e, abs) ->
              let comp' = eval_match e abs in
              small_steps { cs with res = Ready comp' }
          | Ast.Apply (e1, e2) -> (
              let e1' = eval_expression state e1 in
              let e2' = eval_expression state e2 in
              match e1' with
              | Ast.Lambda abs ->
                  let c = substitution e2' abs in
                  small_steps { cs with res = Ready c }
              | Ast.RecLambda (f, (p, c)) as recf ->
                  let c' = substitution e2' (p, c) in
                  let c'' = substitution recf (Ast.PVar f, c') in
                  small_steps { cs with res = Ready c'' }
              | Ast.Var x ->
                  let f = Ast.VariableMap.find x state.builtin_functions in
                  small_steps { cs with res = Ready (f e2') }
              | _ ->
                  Format.printf "Cant apply \ne1 = %t@."
                    (Ast.print_expression e1');
                  assert false )
          | Ast.Out (op, e, c) ->
              let e' = eval_expression state e in
              small_steps
                { cs with ops = (op, e', cs.id) :: cs.ops; res = Ready c }
          | Ast.In (op, e, c) -> (
              match c with
              | Ast.Return _ -> { cs with res = Ready c }
              | Ast.Promise (k, op', abs', var', c') when op = op' ->
                  (* print "inserting in in promise"; *)
                  let comp' = substitution e abs' in
                  let var'' = Ast.Variable.fresh None in

                  let comp'' =
                    match k with
                    | None -> comp'
                    | Some k' ->
                        substitution
                          (Ast.Lambda
                             ( Ast.PTuple [],
                               Ast.Promise
                                 ( k,
                                   op',
                                   abs',
                                   var'',
                                   Ast.Return (Ast.Var var'') ) ))
                          (Ast.PVar k', comp')
                  in
                  small_steps
                    {
                      cs with
                      res =
                        Ready
                          (Ast.Do (comp'', (Ast.PVar var', Ast.In (op, e, c'))));
                    }
              | Ast.Promise (k, op', abs', var', c') ->
                  small_steps
                    {
                      cs with
                      res =
                        Ready
                          (Ast.Promise (k, op', abs', var', Ast.In (op, e, c')));
                    }
              | _ -> (
                  let cs' = small_steps { cs with res = Ready c } in
                  match cs'.res with
                  | Done _ -> cs'
                  | Await c' -> (
                      (* Zgodil se je await. Ne moremo naprej. Moramo iti z Ast.In notri v upanju da najdemo primeren Ast.Promise.*)
                      match c' with
                      | Ast.Do (c1, (p, c2)) ->
                          small_steps
                            {
                              cs' with
                              res =
                                Ready
                                  (Ast.Do
                                     ( Ast.In (op, e, c1),
                                       (p, Ast.In (op, e, c2)) ));
                            }
                      | Ast.Promise _ ->
                          small_steps
                            { cs' with res = Ready (Ast.In (op, e, c')) }
                      | Ast.In _ | Ast.Await _ ->
                          { cs' with res = Await (Ast.In (op, e, c')) }
                      | _ ->
                          (* Here we have:  Return, cant end in await. Match can always do step if we have type. Apply can always do step. Out can always do step. *)
                          assert false )
                  | Ready c' ->
                      (* Zmanjkalo nam je malih korakov *)
                      { cs' with res = Ready (Ast.In (op, e, c')) } ) )
          | Ast.Promise (k, op, abs, p, c) -> (
              let cs' = small_steps { cs with res = Ready c } in
              match cs'.res with
              | Done c' ->
                  {
                    cs' with
                    res = Await (Ast.Promise (k, op, abs, p, Ast.Return c'));
                  }
              | Await c' ->
                  { cs' with res = Await (Ast.Promise (k, op, abs, p, c')) }
              | Ready c' ->
                  { cs' with res = Ready (Ast.Promise (k, op, abs, p, c')) } )
          | Ast.Await (e, abs) as c -> (
              (* print_state state; *)
              match e with
              | Ast.Var _ -> { cs with res = Await c }
              | Ast.Fulfill e' ->
                  let comp' = substitution e' abs in
                  small_steps { cs with res = Ready comp' }
              | _ -> assert false ) )
    else conf_small
  in

  small_steps conf

let resolve_operations (confs : conf list) : conf list * bool =
  (* print "run_rec"; *)
  if debugg then Format.printf "RESOLVE@.";

  let rec take_ops = function
    | [] -> ([], [])
    | c :: cs ->
        let ops', cs' = take_ops cs in
        let ops'' = c.ops in
        let c'' = { c with ops = [] } in
        (ops'' @ ops', c'' :: cs')
  in
  let ops, confs' = take_ops confs in

  if debugg then (
    List.iter print_conf confs';
    List.iter
      (fun (o, e, id) ->
        Format.printf "op=%t, e=%t, id=%i@." (Ast.Operation.print o)
          (Ast.print_expression e) id)
      ops;
    print "press enter to do INSERT";

    try
      let _ = read_int () in
      ()
    with Failure _ -> () );

  List.iter
    (fun (o, e, id) ->
      Format.printf "↑%t %t, id=%i@." (Ast.Operation.print o)
        (Ast.print_expression e) id)
    ops;

  let is_done conf = match conf.res with Ready _ -> false | _ -> true
  and insert_interupts (conf : conf) =
    List.fold_right
      (fun (op, e, id) conf ->
        if id = conf.id then conf
        else
          match conf.res with
          | Done _ -> conf
          | Await c | Ready c -> { conf with res = Ready (Ast.In (op, e, c)) })
      ops conf
  in
  let confs'' = List.map insert_interupts confs' in
  let done' = List.length ops = 0 && List.for_all is_done confs' in
  (confs'', done')

let reset_counters confs : conf list =
  List.map (fun conf -> { conf with counter = 0 }) confs

let rec run_rec state (confs : conf list) : conf list =
  (* print "run_rec"; *)
  (* Ast.print_threads threads; *)
  if debugg then (
    List.iter print_conf confs;
    print "press enter to do BIG steps";
    try
      let _ = read_int () in
      ()
    with Failure _ -> () );

  let confs' = List.map (big_step state) confs in

  (* Here we could remove done configurations and safe them into sam reference *)
  let confs'', done' = resolve_operations confs' in
  match done' with
  | true -> confs''
  | false -> run_rec state (reset_counters confs'')

let run (state : state) (comps : Ast.computation list) : conf list =
  (* print "run"; *)
  let configurations =
    List.mapi (fun id c -> { counter = 0; id; ops = []; res = Ready c }) comps
  in
  run_rec state configurations

let add_external_function x def state =
  {
    state with
    builtin_functions = Ast.VariableMap.add x def state.builtin_functions;
  }

let add_top_let (state : state) (x : Ast.variable) (expr : Ast.expression) =
  { state with toplet = Ast.VariableMap.add x expr state.toplet }
