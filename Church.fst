module Church

type cnat = (#a:Type) -> (a -> a) -> a -> a


let zero            : cnat = fun #a f x -> x
let succ (n : cnat) : cnat = fun #a f x -> n f (f x)

let add  (m n : cnat) : cnat = m succ n
let mult (m n : cnat) : cnat = m (add n) (fun #a -> zero #a)

val fromn : nat -> Tot cnat
let rec fromn n = match n with
    | 0 -> (fun #a -> zero #a)
    | n -> succ (fromn (n - 1))

(* val ton : cnat -> Tot nat *)
(* let ton n = n #nat (fun x -> x + 1) 0 *)

val pred' : (cnat u#a * cnat u#a) -> Tot (cnat u#a * cnat u#a)
let pred' (a, b) = (succ b, a)

val pred : cnat u#(1 + a) -> cnat u#a
let pred m = let (_, x) = (m pred' ((fun #a -> zero #a), (fun #a -> zero #a))) in x

let ten = fromn 10
let hund = mult ten ten
let thou = mult ten hund
let x = mult hund (mult hund hund)
let y = mult thou thou

let _ = assert_norm (x #nat (fun x -> x + 1) 0 == y #nat (fun x -> x + 1) 0)
