type nat = Zero | Succ of nat

let rec add = fun a b -> match a with
  | Zero -> b
  | Succ a' -> Succ (add a' b)

let main = add (Succ(Succ(Zero))) (Succ((Zero)))