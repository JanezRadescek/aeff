open Utils

exception PatternMismatch

let print s = Format.printf "%s@." s

type value =
  | Const of Const.t
  | Tuple of value list
  | Variant of Ast.label * value option
  | Fulfill of value
  | Reference of value ref
  | Closure of (value -> result)

and result =
  | Done of value
  | Await of Ast.computation
  | Ready of Ast.computation

type vars = Ast.expression Ast.VariableMap.t

let initial_state = Ast.VariableMap.empty

let extend_variables (state : vars) vars : vars =
  List.fold_left
    (fun state' (x, var) -> Ast.VariableMap.add x var state')
    state vars

type conf = {
  counter : int;
  id : int;
  ops : (Ast.operation * Ast.expression * int) list;
  interupts : (Ast.operation * Ast.expression) list;
  vars : vars;
  res : result;
}

(* type conf_small = {
   counter : int;
   ops : (Ast.operation * Ast.expression * int) list;
   vars : vars;
   comp : Ast.computation;
   } *)

let rec eval_value (state : vars) (expr : Ast.expression) : value =
  match expr with
  | Ast.Var x -> eval_value state (Ast.VariableMap.find x state)
  | Ast.Const c -> Const c
  | Ast.Annotated (e, _a) -> eval_value state e
  | Ast.Tuple es -> Tuple (List.map (eval_value state) es)
  | Ast.Variant (lbl, None) -> Variant (lbl, None)
  | Ast.Variant (lbl, Some e) -> Variant (lbl, Some (eval_value state e))
  | Ast.Lambda abs -> eval_abstraction state abs
  | Ast.RecLambda _ -> failwith "TODO"
  | Ast.Fulfill e -> Fulfill (eval_value state e)
  | Ast.Reference e -> Reference (ref (eval_value state !e))

and eval_abstraction (_state : vars) ((_p, _c) : Ast.abstraction) =
  Closure (fun _v -> failwith "TODO")



(* eval_comp : state -> computation -> result
   | Apply (e1, e2) ->
      let v1 = eval_value state e1
      and v2 = eval_value state e2 in
      match v1 with
      | Closure f -> f v2
      | _ -> failwith "Closure expected in application"

   let eval_abstraction state (p, c) =
   fun v ->
    let state' = extend_state state p v in
    eval_comp state' c *)


(* let intersection_compliment aa bb =
   ( List.filter (fun (a1, _a2) -> List.mem a1 bb) aa,
    List.filter (fun b -> not (List.mem_assoc b aa)) bb ) *)

(* let rec eval_tuple state = function
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
*)


let substitution state (v : value) ((x, m) : Ast.abstraction) :
  vars * Ast.computation =
  let vars = match_pattern_with_expression state x v in
  let state' = extend_variables state vars in
  (state', m) 

(* let rec eval_expression state expr : Ast.expression =
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
   | Ast.Reference e -> Ast.Reference (ref (eval_expression state !e)) *)

(* let rec eval_function state f arg : state * Ast.computation =
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
          Format.printf "eval_expresion %t -->> %t@." (Ast.print_expression arg)
            (Ast.print_expression arg');
          (state, f' arg') )
   | Ast.Annotated (e, _ty) -> eval_function state e arg
   | expr ->
      Error.runtime "Function expected but got %t" (Ast.print_expression expr)

*)

   let rec eval_match vars e abs =
   match abs with
   | [] -> assert false
   | x :: xs -> (
      try substitution vars e x with PatternMismatch -> eval_match vars e xs ) 

let starting_state = ref initial_state

let print_state (state : vars) =
  Ast.VariableMap.iter
    (fun k v ->
       match Ast.VariableMap.find_opt k !starting_state with
       | None ->
         Format.printf "key=%t value=%t@." (Ast.Variable.print k)
           (Ast.print_expression v)
       | Some _v -> ())
    state

(* let rec eval_fulfill state (e : Ast.expression) =
   match e with
   | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state.variables with
      | None -> None
      | Some e' -> (
          match eval_fulfill state e' with
          | None -> None
          | Some e'' ->
              (* Format.printf "Found %t" (Ast.print_expression e''); *)
              Some (eval_expression state e'') ) )
   | Ast.Fulfill e -> Some e
   | _ -> assert false *)

(* let run_comp state comp : comp_state * result =
   (* print "run_comp start"; *)
   let rec run_comp_rec (state : comp_state) (comp : Ast.computation) :
    comp_state * result =
    print_state state.state;
    Format.printf "comp = %t\n@." (Ast.print_computation comp);
    if false then (
      print "press anything to continiue";
      try
        let _ = read_int () in
        ()
      with Failure _ -> () );
    (* If exit code_is done parent might be do and we still have some work to do. on the contrary we will triger waiting only when we realy have to stop
       the problem before was we could come to promise somewhere in recursion and not realize it and call on same computation again not reazing we are not doing steps *)
    if state.counter < 1000 then
      let state = { state with counter = state.counter - 1 } in
      match comp with
      | Ast.Return expr -> (state, Done expr)
      | Ast.Do (Ast.Return e, abs) ->
        let vars', comp' = substitution state.vars e abs in
        run_comp_rec { state with vars = vars' } comp'
      | Ast.Do (Ast.Promise (op, abs, p, c), abs') ->
        run_comp_rec state (Ast.Promise (op, abs, p, Ast.Do (c, abs')))
      | Ast.Do (c, abs) -> (
          let state', res = run_comp_rec state c in
          match res with
          | Done expr ->
            let vars', comp' = substitution state'.vars expr abs in
            run_comp_rec { state' with vars = vars' } comp'
          | Await comp' -> (state', Await (Ast.Do (comp', abs)))
          | Ready comp' -> (state', Ready (Ast.Do (comp', abs))) )
      | Ast.Match (e, abs) ->
        let vars', comp = eval_match state.vars e abs in
        run_comp_rec state' comp
      | Ast.Apply (e1, e2) ->
        print "applying";
        let state', e1e2 = eval_function state e1 e2 in
        run_comp_rec state' e1e2
      | Ast.Out (op, e, c) ->
        let e' = eval_expression state.vars e in
        (* we need actual value not some variable. Variable in other thread might not even exist or have complitly different mining. *)
        run_comp_rec { state with ops = (op, e', id) :: state.ops } c
      | Ast.In (op, e, c) -> (
          match c with
          | Ast.Return _ -> Done (state, c)
          | Ast.Promise (op', abs', var', c') when op = op' ->
            (* print "inserting in in promise"; *)
            let state', comp' = substitution state e abs' in
            run_comp_rec state'
              (Ast.Do (comp', (Ast.PVar var', Ast.In (op, e, c'))))
          | Ast.Promise (op', abs', var', c') ->
            let state', c'' = run_comp_rec state c' in
            run_comp_rec state'
              (Ast.Promise (op', abs', var', Ast.In (op, e, c'')))
          | _ -> (
              let state', c' = run_comp_rec state c in
              match c' with
              | Ast.Return _ -> (state', c')
              | _ ->
                (*Here we can get promise op, but it is rare so its ok to wait for next run_comp*)
                (state', Ast.In (op, e, c')) ) )
      | Ast.Promise (op, abs, p, c) ->
        let state', comp' = run_comp_rec state c in
        (state', Ast.Promise (op, abs, p, comp'))
      | Ast.Await (e, abs) -> (
          (* print_state state; *)
          match eval_fulfill state e with
          | None ->
            exit_code := Ast.Waiting;
            (state, comp)
          | Some e' ->
            let state', comp' = substitution state e' abs in
            run_comp_rec state' comp' )
    else (state, comp)
   in

   let state', comp' = run_comp_rec state comp in
   (* print "run_comp end"; *)
   (state', comp', !exit_code, !ops) *)

(* match comp' with
   | Ast.Return e ->
   (state', Ast.Return (eval_expression state' e), Ast.Done, !ops)
   | Ast.In _ -> (state', comp', Ast.Waiting, !ops)
   | Ast.Promise _ -> (state', comp', Ast.Waiting, !ops)
   | _ ->
   Format.printf "THIS SHOULD NOT HAPPEN = %t@."
    (Ast.print_computation comp');
   assert false *)

(* let run_thread (state : state) ((comp, id, condition) : Ast.thread) :
   state * Ast.thread * (Ast.operation * Ast.expression * int) list =
   (* print "run_thread"; *)
   match condition with
   | Ast.Ready ->
    let state', comp', condition', ops = run_comp state comp id in
    (state', (comp', id, condition'), ops)
   | _ -> (state, (comp, id, condition), []) *)

let big_step (conf : conf) : conf =
  let rec small_steps (conf_small:conf) : conf =
    print_state conf_small.vars;
    Format.printf "comp = %t\n@." (Ast.print_computation conf_small.comp);
    if false then (
      print "press anything to continiue";
      try
        let _ = read_int () in
        ()
      with Failure _ -> () );
    (* If exit code_is done parent might be do and we still have some work to do. on the contrary we will triger waiting only when we realy have to stop
       the problem before was we could come to promise somewhere in recursion and not realize it and call on same computation again not reazing we are not doing steps *)
    if conf_small.counter < 1000 then
      let cs = { conf_small with counter = conf_small.counter + 1 } in
      match cs.res with
      | Done _ -> cs
      | Await _ -> cs
      | Ready comp ->
        (
          match comp with
          | Ast.Return e -> let v = eval_value cs.vars e in {cs with res = Done v}
          | Ast.Do (Ast.Return e, abs) ->
            let v = eval_value cs.vars e in
            let vars', comp' = substitution cs.vars v abs in
            small_steps { cs with vars = vars'; res = Ready comp' }
          | Ast.Do (Ast.Promise (op, abs, p, c), abs') ->
            small_steps {cs with res = Ready (Ast.Promise (op, abs, p, Ast.Do (c, abs')))}
          | Ast.Do (c, abs) -> (
              let cs' = small_steps {cs with res = Ready c} in
              (match cs'.res with
               | Done v ->
                 let vars', comp' = substitution cs'.vars v abs in
                 small_steps { cs' with vars = vars'; res = Ready comp'}
               | Await _ | Ready _ -> cs'))
          | Ast.Match (e, abs) ->
            let v = eval_value cs.vars e in
            let vars', comp' = eval_match cs.vars v abs in
            small_steps { cs with vars = vars'; res = Ready comp'}
          | Ast.Apply (e1, e2) ->
            print "applying";
            let state', e1e2 = eval_function state e1 e2 in
            run_comp_rec state' e1e2
          | Ast.Out (op, e, c) ->
            let e' = eval_expression state.vars e in
            (* we need actual value not some variable. Variable in other thread might not even exist or have complitly different mining. *)
            run_comp_rec { state with ops = (op, e', id) :: state.ops } c
          | Ast.In (op, e, c) -> (
              match c with
              | Ast.Return _ -> Done (state, c)
              | Ast.Promise (op', abs', var', c') when op = op' ->
                (* print "inserting in in promise"; *)
                let state', comp' = substitution state e abs' in
                run_comp_rec state'
                  (Ast.Do (comp', (Ast.PVar var', Ast.In (op, e, c'))))
              | Ast.Promise (op', abs', var', c') ->
                let state', c'' = run_comp_rec state c' in
                run_comp_rec state'
                  (Ast.Promise (op', abs', var', Ast.In (op, e, c'')))
              | _ -> (
                  let state', c' = run_comp_rec state c in
                  match c' with
                  | Ast.Return _ -> (state', c')
                  | _ ->
                    (*Here we can get promise op, but it is rare so its ok to wait for next run_comp*)
                    (state', Ast.In (op, e, c')) ) )
          | Ast.Promise (op, abs, p, c) ->
            let state', comp' = run_comp_rec state c in
            (state', Ast.Promise (op, abs, p, comp'))
          | Ast.Await (e, abs) -> (
              (* print_state state; *)
              match eval_fulfill state e with
              | None ->
                exit_code := Ast.Waiting;
                (state, comp)
              | Some e' ->
                let state', comp' = substitution state e' abs in
                run_comp_rec state' comp' )
        )




    else conf_small
  in

  match conf.computation with
  | Done _ -> conf
  | _ -> failwith "TODO call small steps here"

let resolve_operations (confs : conf list) : conf list * bool =
  (* print "run_rec"; *)
  let finished = ref true in

  let rec take_ops = function
    | [] -> ([], [])
    | c :: cs ->
      let ops', cs' = take_ops cs in
      let ops'' = c.ops in
      let c'' = { c with ops = [] } in
      (ops'' @ ops', c'' :: cs')
  in

  let ops, confs' = take_ops confs in

  let insert_interupts (conf : conf) =
    (match conf.computation with Ready _ -> finished := false | _ -> ());
    List.fold_right
      (fun (op, e, id) conf ->
         if id = conf.id then conf
         else { conf with interupts = (op, e) :: conf.interupts })
      ops conf
  in

  let done' = List.length ops = 0 && !finished in
  (List.map insert_interupts confs', done')

let rec run_rec (confs : conf list) : conf list =
  (* print "run_rec"; *)
  (* Ast.print_threads threads; *)
  let confs' = List.map big_step confs in
  (* Here we could remove done configurations and safe them into sam reference *)
  let confs'', done' = resolve_operations confs' in
  match done' with true -> confs'' | false -> run_rec confs''

let run (state : vars) (comps : Ast.computation list) =
  (* print "run"; *)
  (* starting_state := state; *)
  let i = ref 0 in
  let configurations =
    List.map
      (fun c ->
         let id = !i in
         incr i;

         {
           counter = 1000;
           id;
           ops = [];
           interupts = [];
           vars = state;
           computation = Ready c;
         })
      comps
  in
  run_rec configurations

(* It might happen some part of code has never run and as such variable is not in state
   let rec try_eval_expression state expr =
   match expr with
   | Ast.Var x -> (
      match Ast.VariableMap.find_opt x state with
      | Some e -> try_eval_expression state e
      | None -> expr )
   | Ast.Const _ -> expr
   | Ast.Annotated (e, _a) -> try_eval_expression state e
   | Ast.Tuple _ ->
    Ast.Tuple (List.map (try_eval_expression state) (eval_tuple state expr))
   | Ast.Variant (lbl, Some e) ->
    Ast.Variant (lbl, Some (try_eval_expression state e))
   | Ast.Variant (lbl, None) -> Ast.Variant (lbl, None)
   | Ast.Lambda _ | Ast.RecLambda _ -> expr
   | Ast.Fulfill e -> Ast.Fulfill (try_eval_expression state e)
   | Ast.Reference e -> Ast.Reference (ref (try_eval_expression state !e))

   unlike prints in ast this have state and TRIES to convert variables to expressions
   let rec print_computation ?max_level state c ppf =
   let print ?at_level = Print.print ?max_level ?at_level ppf in
   match c with
   | Ast.Return e ->
    print ~at_level:1 "return %t"
      (Ast.print_expression ~max_level:0 (try_eval_expression state e))
   | Ast.Do (c1, (PNonbinding, c2)) ->
    print "@[<hov>%t;@ %t@]"
      (print_computation state c1)
      (print_computation state c2)
   | Ast.Do (c1, (pat, c2)) ->
    print "@[<hov>let@[<hov>@ %t =@ %t@] in@ %t@]" (Ast.print_pattern pat)
      (print_computation state c1)
      (print_computation state c2)
   | Match (e, lst) ->
    print "match %t with (@[<hov>%t@])"
      (Ast.print_expression (try_eval_expression state e))
      (Print.print_sequence " | " (case state) lst)
   | Apply (e1, e2) ->
    print ~at_level:1 "@[%t@ %t@]"
      (Ast.print_expression ~max_level:1 (try_eval_expression state e1))
      (Ast.print_expression ~max_level:0 (try_eval_expression state e2))
   | In (op, e, c) ->
    print "↓%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
      (Ast.print_expression (try_eval_expression state e))
      (print_computation state c)
   | Out (op, e, c) ->
    print "↑%t(@[<hv>%t,@ %t@])" (Ast.Operation.print op)
      (Ast.print_expression (try_eval_expression state e))
      (print_computation state c)
   | Promise (op, (p1, c1), p2, c2) ->
    print "@[<hv>promise (@[<hov>%t %t ↦@ %t@])@ as %t in@ %t@]"
      (Ast.Operation.print op) (Ast.print_pattern p1)
      (print_computation state c1)
      (Ast.Variable.print p2)
      (print_computation state c2)
   | Await (e, (p, c)) ->
    print "@[<hov>await @[<hov>%t until@ ⟨%t⟩@] in@ %t@]"
      (Ast.print_expression (try_eval_expression state e))
      (Ast.print_pattern p)
      (print_computation state c)

   and print_abstraction state (p, c) ppf =
   Format.fprintf ppf "%t ↦ %t" (Ast.print_pattern p)
    (print_computation state c)

   and case state (a : Ast.abstraction) (ppf : Format.formatter) =
   Format.fprintf ppf "%t" (print_abstraction state a) *)

(* let print_thread (state : state) (thread : Ast.thread) : unit =
   let comp, id, _cond = thread in
   Format.printf "Thread %i %t@." id (print_computation state comp) *)

let add_external_function x def state = Ast.VariableMap.add x def state

let eval_top_let (state : vars) (x : Ast.variable) (expr : Ast.expression) =
  Ast.VariableMap.add x expr state
