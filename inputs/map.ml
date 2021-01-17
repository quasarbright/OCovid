type 'a list = Empty | Cons of 'a * 'a list

let rec map = fun f xs -> match xs with
  | Empty -> Empty
  | Cons(x,xs) -> Cons(f x, map f xs)

type bool = True | False

let not = fun b -> match b with
  | True -> False
  | False -> True

let main = map not (Cons(True,Cons(False,Cons(True,Empty))))
