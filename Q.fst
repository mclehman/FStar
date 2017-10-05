module Q

let x : term = `(3)
let y : term = `(3)

// False, we don't encode quoted terms, but we should
(* let _ = assert (x == y) *)

open FStar.Tactics

let z : int =
    synth_by_tactic (exact (return (`(8))))
