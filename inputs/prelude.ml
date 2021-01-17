type 'a list = Empty | Cons of 'a * 'a list
type bool = True | False
type 'a option = None | Some of 'a
type ('a,'b) result = Ok of 'a | Error of 'b

let flip = fun f x y -> f y x
let curry = fun f x y -> f (x,y)
let uncurry = fun f xy -> match xy with (x,y) -> f x y
let compose = fun f g x -> f (g x)


let fst = fun xy -> match xy with (a,b) -> a
let snd = fun xy -> match xy with (a,b) -> b

let first = fun f pair -> match pair with (a,b) -> (f a,b)
let second = fun f pair -> match pair with (a,b) -> (a,f b)

let rec zip = fun xs ys -> match (xs,ys) with
  | (Empty,ys) -> Empty
  | (xs,Empty) -> Empty
  | (Cons(x,xs),Cons(y,ys)) -> Cons((x,y),zip xs ys)

let rec unzip = fun pairs -> match pairs with
  | Empty -> (Empty,Empty)
  | Cons((x,y),pairs) ->
    (match unzip pairs with (xs,ys) -> (Cons(x,xs),Cons(y,ys)))

let rec foldr = fun f z xs -> match xs with
  | Empty -> z
  | Cons(x,xs) -> f x (foldr f z xs)

let map = fun f -> foldr (fun x ys -> Cons(f x,ys)) Empty

let append = flip (foldr (fun x y -> Cons(x,y)))

let concat = foldr append Empty

let concatMap = fun f xs -> concat (map f xs)

let fromOption = fun a ma -> match ma with None -> a | Some a -> a

let fromResult = fun fl fr e -> match e with Error l -> fl l | Ok r -> fr r

let listBind = flip concatMap
let optionBind = fun ma k -> match ma with
  | None -> None
  | Some a -> k a
let eitherBind = fun ma k -> match ma with
  | Error err -> Error err
  | Ok a -> k a


let not = fun b -> match b with True -> False | False -> True
let and_ = fun a b -> match a with True -> b | False -> False
let or_ = fun a b -> not (and_ (not a) (not b))
let xor = fun a b -> and_ (or_ a b) (not (and_ a b))