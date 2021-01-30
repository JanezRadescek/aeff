open Utils

exception PatternMismatch

let print s = Format.printf "%s@." s

(* type value =
   | Const of Const.t
   | Tuple of value list
   | Variant of Ast.label * value option
   | Fulfill of value
   | Reference of value ref
   | Closure of (value -> Ast.computation) *)

type result =
  | Done of Ast.expression
  | Await of Ast.computation
  | Ready of Ast.computation

type state = {
  toplet : Ast.expression Ast.VariableMap.t;
  builtin_functions : (Ast.expression -> Ast.computation) Ast.VariableMap.t;
}

let initial_state =
  { toplet = Ast.VariableMap.empty; builtin_functions = Ast.VariableMap.empty }

(* let extend_variables (state : vars) vars : vars =
   List.fold_left
    (fun state' (x, var) -> Ast.VariableMap.add x var state')
    state vars *)

type conf = {
  counter : int;
  id : int;
  ops : (Ast.operation * Ast.expression * int) list;
  (* interupts : (Ast.operation * Ast.expression) list; *)
  res : result;
}

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
  Ast.substitute_computation subst' m

(* let rec eval_value (state : vars) (expr : Ast.expression) : value =
   match expr with
   | Ast.Var x -> Ast.VariableMap.find x state
   | Ast.Const c -> Const c
   | Ast.Annotated (e, _a) -> eval_value state e
   | Ast.Tuple es -> Tuple (List.map (eval_value state) es)
   | Ast.Variant (lbl, None) -> Variant (lbl, None)
   | Ast.Variant (lbl, Some e) -> Variant (lbl, Some (eval_value state e))
   | Ast.Lambda abs -> eval_abstraction state abs
   | Ast.RecLambda _ -> failwith "TODO"
   | Ast.Fulfill e -> Fulfill (eval_value state e)
   | Ast.Reference e -> Reference (ref (eval_value state !e)) *)

(* and eval_abstraction (_vars : vars) ((_p, _c) : Ast.abstraction) : value =
   Closure (fun _v -> failwith "TODO") *)

let rec eval_match (e : Ast.expression) abs : Ast.computation =
  match abs with
  | [] -> assert false
  | x :: xs -> (
      try substitution e x with PatternMismatch -> eval_match e xs )

let starting_state = ref initial_state

(*
  let print_state (state : vars) =
   Ast.VariableMap.iter
    (fun k v ->
       match Ast.VariableMap.find_opt k !starting_state with
       | None ->
         Format.printf "key=%t value=%t@." (Ast.Variable.print k)
           (Ast.print_expression v)
       | Some _v -> ())
    state *)

let eval_fulfill (e : Ast.expression) =
  match e with
  | Ast.Var _x -> None
  | Ast.Fulfill e -> Some e
  | _ -> assert false

let big_step (conf : conf) : conf =
  let rec small_steps (conf_small : conf) : conf =
    (* print_state conf_small.vars; *)
    (* Format.printf "comp = %t\n@." (Ast.print_computation conf_small.res); *)
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
      | Ready comp -> (
          match comp with
          | Ast.Return e -> { cs with res = Done e }
          | Ast.Do (Ast.Return e, abs) ->
              let comp' = substitution e abs in
              small_steps { cs with res = Ready comp' }
          | Ast.Do (Ast.Promise (op, abs, p, c), abs') ->
              small_steps
                {
                  cs with
                  res = Ready (Ast.Promise (op, abs, p, Ast.Do (c, abs')));
                }
          | Ast.Do (c, abs) -> (
              let cs' = small_steps { cs with res = Ready c } in
              match cs'.res with
              | Done e ->
                  let comp' = substitution e abs in
                  small_steps { cs' with res = Ready comp' }
              | Await c' -> { cs' with res = Await (Ast.Do (c', abs)) }
              | Ready c' -> { cs' with res = Ready (Ast.Do (c', abs)) } )
          | Ast.Match (e, abs) ->
              let comp' = eval_match e abs in
              small_steps { cs with res = Ready comp' }
          | Ast.Apply (e1, e2) -> (
              match e1 with
              | Ast.Lambda abs ->
                  let c = substitution e2 abs in
                  small_steps { cs with res = Ready c }
              | Ast.RecLambda (_f, _abs) -> failwith "TODO"
              | _ -> assert false )
          | Ast.Out (op, e, c) ->
              small_steps
                { cs with ops = (op, e, cs.id) :: cs.ops; res = Ready c }
          | Ast.In (op, e, c) -> (
              match c with
              | Ast.Return _ -> { cs with res = Ready c }
              | Ast.Promise (op', abs', var', c') when op = op' ->
                  (* print "inserting in in promise"; *)
                  let comp' = substitution e abs' in
                  small_steps
                    {
                      cs with
                      res =
                        Ready
                          (Ast.Do (comp', (Ast.PVar var', Ast.In (op, e, c'))));
                    }
              | Ast.Promise (op', abs', var', c') ->
                  small_steps
                    {
                      cs with
                      res =
                        Ready
                          (Ast.Promise (op', abs', var', Ast.In (op, e, c')));
                    }
              | _ -> (
                  let cs' = small_steps { cs with res = Ready c } in
                  match cs'.res with
                  | Done _ -> small_steps cs'
                  | Await c' -> { cs' with res = Await (Ast.In (op, e, c')) }
                  | Ready c' -> { cs' with res = Ready (Ast.In (op, e, c')) } )
              )
          | Ast.Promise (op, abs, p, c) -> (
              let cs' = small_steps { cs with res = Ready c } in
              match cs'.res with
              | Done _ -> small_steps cs'
              | Await c' ->
                  { cs' with res = Await (Ast.Promise (op, abs, p, c')) }
              | Ready c' ->
                  { cs' with res = Ready (Ast.Promise (op, abs, p, c')) } )
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
    (match conf.res with Ready _ -> finished := false | _ -> ());
    List.fold_right
      (fun (op, e, id) conf ->
        if id = conf.id then conf
        else
          match conf.res with
          | Done _ -> conf
          | Await c | Ready c -> { conf with res = Ready (Ast.In (op, e, c)) })
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

let run (state : state) (comps : Ast.computation list) : conf list =
  (* print "run"; *)
  (* starting_state := state; *)
  starting_state := state;
  let i = ref 0 in
  let configurations =
    List.map
      (fun c ->
        let id = !i in
        incr i;

        { counter = 1000; id; ops = []; res = Ready c })
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

let print_conf conf =
  Format.printf "Conf id = %d; res = %t@." conf.id
    ( match conf.res with
    | Done e -> Ast.print_expression e
    | Await c | Ready c -> Ast.print_computation c )

let add_external_function x def state =
  {
    state with
    builtin_functions = Ast.VariableMap.add x def state.builtin_functions;
  }

let add_top_let (state : state) (x : Ast.variable) (expr : Ast.expression) =
  { state with toplet = Ast.VariableMap.add x expr state.toplet }
