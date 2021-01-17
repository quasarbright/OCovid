type nat = Zero | Succ of nat

let rec add = fun a b -> match a with
  | Zero -> b
  | Succ a' -> Succ (add a' b)

let rec fib = fun n -> match n with
  | Zero -> Succ Zero
  | Succ Zero -> Succ Zero
  | Succ (Succ n') -> add (fib n') (fib (Succ n'))

(* 1 1 2 3 5 8 13 ... *)

(* fib 6 == 13 *)
let six = Succ(Succ(Succ(Succ(Succ(Succ Zero)))))
let main = fib six