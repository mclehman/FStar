module Crash

open FStar.Tactics

type qn = list string
type var = string

type pattern =
| SPAny: pattern
| SPVar: var: var -> pattern
| SPQn: qn: qn -> pattern
| SPApp: hd: pattern -> arg: pattern -> pattern

noeq type match_exception =
| NameMismatch of qn * qn
| SimpleMismatch of pattern * term
| NonLinearMismatch of var * term * term
| UnsupportedTermInPattern of term

let string_of_match_exception = function _ -> ""

noeq type match_res a =
| Success of a
| Error of match_exception

let dm4f_match_res (a:Type) = unit -> M (match_res a)

let return_match_res a (x: a) : dm4f_match_res a =
  fun _ -> Success x

let bind_match_res (a b: Type)
                   (f: dm4f_match_res a)
                   (g: a -> dm4f_match_res b)
    : dm4f_match_res b =
  fun _ ->
    let r = f () in
    match r with
    | Success aa -> g aa ()
    | Error ex -> Error ex

let raise_match_res a (ex: match_exception) : dm4f_match_res a =
  fun _ -> Error ex

reifiable reflectable new_effect {
  EXN : (a:Type) -> Effect
  with repr     = dm4f_match_res
     ; bind     = bind_match_res
     ; return   = return_match_res
     ; raise (#a:Type) = raise_match_res a
}

let raise =
  EXN?.raise
effect Exn (a:Type) (pre:Type0) (post:EXN?.post a) =
  EXN a (fun (_:unit) (p:EXN?.post a) -> pre /\
          (forall (r: match_res a). (pre /\ post r) ==> p r))
effect Ex (a:Type) =
  EXN a (fun _ p -> forall x. p x)

let lift_exn_tac #a #b (f: a -> Ex b) (aa: a) : Tac b =
  match reify (f aa) () with
  | Success bb -> Tactics.return bb ()
  | Error ex -> Tactics.fail (string_of_match_exception ex) ()

type bindings = list (var * term)

let rec interp_pattern_tr
        (pat: pattern) (tm: term) (cur_bindings: bindings)
    : Ex bindings =
  match pat with
  | SPAny ->
    []
  | SPVar var ->
    (match List.Tot.assoc var cur_bindings with
     | Some tm' -> if term_eq tm tm' then cur_bindings
                  else raise (NonLinearMismatch (var, tm, tm'))
     | None -> ((var, tm) :: cur_bindings))
  | SPQn qn -> begin
    match inspect tm with
    | Tv_FVar fv ->
      if inspect_fv fv = qn then cur_bindings
      else raise (NameMismatch (qn, (inspect_fv fv)))
    | _ -> raise (SimpleMismatch (pat, tm)) end
  | SPApp p_hd p_arg -> begin
    match inspect tm with
    | Tv_App hd (arg, _) ->
      let with_hd = interp_pattern_tr p_hd hd cur_bindings in
      let with_arg = interp_pattern_tr p_arg arg with_hd in
      with_arg
    | _ -> raise (SimpleMismatch (pat, tm)) end

let interp_pattern (pat: pattern) (tm: term) : Ex bindings =
  List.Tot.rev (interp_pattern_tr pat tm [])

let rec pattern_of_term_ex tm : Ex pattern =
  match inspect tm with
  | Tv_Var bv -> SPVar (inspect_bv bv)
  | Tv_FVar fv -> SPQn (inspect_fv fv)
  | Tv_App f (x, _) ->
    SPApp (pattern_of_term_ex f) (pattern_of_term_ex x)
  | _ -> raise (UnsupportedTermInPattern tm)

let beta_reduce (tm: term) : Tac term =
  norm_term [] tm ()

let pattern_of_term tm : Tac pattern =
  lift_exn_tac pattern_of_term_ex (beta_reduce tm)

let rec binders_and_body_of_abs tm : binders * term =
  match inspect tm with
  | Tv_Abs binder tm ->
    let binders, body = binders_and_body_of_abs tm in
    binder :: binders, body
  | _ -> [], tm

let pattern_of_abs tm : Tac pattern =
  let binders, body = binders_and_body_of_abs tm in
  pattern_of_term body

let match_term pat tm : Tac bindings =
  lift_exn_tac (interp_pattern pat) tm

let match_goal pat : Tac bindings =
  match_term pat (cur_goal ())

let test () =
  assert_by_tactic (1 == 1)
    (fun () ->
      let pat = quote (fun (x: int) -> x == x) () in
      let compiled = pattern_of_abs pat in
      let bindings = match_goal compiled in
      trefl ())
