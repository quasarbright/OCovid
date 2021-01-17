import Test.Hspec
import Test.Hspec.Expectations

import qualified Data.Map as Map
import Data.Map(Map)

import OCovid.Parsing.Parse
import OCovid.Syntax.Expr
import OCovid.Syntax.Program
import OCovid.Static.Types

import OCovid.Static.Typing

import qualified Data.Map as Map
import Data.Function ((&))
import Control.Arrow (second)
import Control.Monad (unless)

import qualified OCovid.Static.WellFormedness as WF

expectTrue :: HasCallStack => String -> Bool -> Expectation
expectTrue msg b = unless b (expectationFailure msg)

compareWith :: (HasCallStack, Show a) => (a -> a -> Bool) -> String -> a -> a -> Expectation
compareWith comparator errorDesc result expected = expectTrue errorMsg (comparator expected result)
  where
    errorMsg = show result ++ " " ++ errorDesc ++ " " ++ show expected

inferExprString :: String -> Either TypeError Type
inferExprString src = case parseExpr "test/Spec.hs" src of
    Left err -> Left (InternalError err)
    Right e -> case inferAndFinalizeExpr e of
        Left err -> Left err
        Right t -> Right (simplifyMono t)

inferProgramString :: String -> Either TypeError (Map String Type)
inferProgramString src = case parseProgram "test/Spec.hs" src of
     Left err -> Left (InternalError err)
     Right e -> case typeCheckProgram e of
         Left err -> Left err
         Right m -> m & Map.map blindInstantiate & Right

shouldContainMap :: (HasCallStack, Ord a, Show a, Show b, Eq b) => Map a b -> Map a b -> Expectation
shouldContainMap = compareWith Map.isSubmapOf "does not contain"

shouldProgInfer :: HasCallStack => String -> Either TypeError [(String, Type)] -> Expectation
shouldProgInfer src result = case (inferProgramString src, fmap Map.fromList result) of
    (Right res, Right res') -> shouldContainMap res res'
    (x,y) -> shouldBe x y

wfExprString :: String -> [WF.WFError]
wfExprString src = case parseExpr "test/Spec.hs" src of
    Left err -> [WF.InternalError err]
    Right e -> WF.executeChecker (WF.checkExpr e)

wfProgString :: String -> [WF.WFError]
wfProgString src = case parseProgram "test/Spec.hs" src of
    Left err -> [WF.InternalError err]
    Right e -> WF.executeChecker (WF.checkProgram e)
        

stdTypes = unlines
    [ "type 'a list = Empty | Cons of 'a * 'a list"
    , "type bool = True | False"
    , "type nat = Zero | Succ of nat"
    ]

stdLib = stdTypes ++ unlines
    [ "let not = fun b -> match b with True -> False | False -> True"
    ]

main :: IO ()
main = hspec $ do
    describe "type checker" $ do
        it "infers tuple types" $ do
            inferExprString "()" `shouldBe` Right tunit
            inferExprString "((),())" `shouldBe` Right (ttuple [tunit, tunit])
            inferExprString "((),((),()))" `shouldBe` Right (ttuple [tunit, ttuple [tunit, tunit]])
        it "infers function types" $ do
            inferExprString "fun x -> x" `shouldBe` Right (tvar "a" \-> tvar "a")
            inferExprString "fun x -> ()" `shouldBe` Right (tvar "a" \-> tunit)
            inferExprString "fun x y -> x" `shouldBe` Right (tvar "a" \-> tvar "b" \-> tvar "a")
            -- assoc
            inferExprString "fun t -> match t with | ((x,y),z) -> (x,(y,z))" `shouldBe` Right (ttuple [ttuple [tvar "a", tvar "b"], tvar "c"] \-> ttuple [tvar "a", ttuple [tvar "b", tvar "c"]])
        it "infers higher order function types" $ do
            -- .
            inferExprString "fun f g x -> f (g x)" `shouldBe` Right ((tvar "a" \-> tvar "b") \-> (tvar "c" \-> tvar "a") \-> tvar "c" \-> tvar "b")
            -- $
            inferExprString "fun f x -> f x" `shouldBe` Right ((tvar "a" \-> tvar "b") \-> tvar "a" \-> tvar "b")
            -- &
            inferExprString "fun x f -> f x" `shouldBe` Right (tvar "a" \-> (tvar "a" \-> tvar "b") \-> tvar "b")
            -- const
            inferExprString "fun a b -> a" `shouldBe` Right (tvar "a" \-> tvar "b" \-> tvar "a")
            inferExprString "(fun a b -> a) ()" `shouldBe` Right (tvar "a" \-> tunit)
            -- flip
            inferExprString "fun f x y -> f y x" `shouldBe` Right ((tvar "a" \-> tvar "b" \-> tvar "c") \-> tvar "b" \-> tvar "a" \-> tvar "c")
            -- curry
            inferExprString "fun f x y -> f (x,y)" `shouldBe` Right ((ttuple [tvar "a", tvar "b"] \-> tvar "c") \-> tvar "a" \-> tvar "b" \-> tvar "c")
            -- uncurry
            inferExprString "fun f xy -> match xy with | (x,y) -> f x y" `shouldBe` Right ((tvar "a" \-> tvar "b" \-> tvar "c") \-> ttuple [tvar "a", tvar "b"] \-> tvar "c")
            --- ***
            inferExprString "fun f g xy -> match xy with | (x,y) -> (f x, g y)" `shouldBe` Right ((tvar "a" \-> tvar "b") \-> (tvar "c" \-> tvar "d") \-> ttuple [tvar "a", tvar "c"] \-> ttuple [tvar "b", tvar "d"])
            -- &&&
            inferExprString "fun f g x -> (f x, g x)" `shouldBe` Right ((tvar "a" \-> tvar "b") \-> (tvar "a" \-> tvar "c") \-> tvar "a" \-> ttuple [tvar "b", tvar "c"])
            -- first
            inferExprString "fun f xy -> match xy with | (x,y) -> (f x, y)" `shouldBe` Right ((tvar "a" \-> tvar "b") \-> ttuple [tvar "a", tvar "c"] \-> ttuple [tvar "b", tvar "c"])
            -- second
            inferExprString "fun f xy -> match xy with | (x,y) -> (x, f y)" `shouldBe` Right ((tvar "a" \-> tvar "b") \-> ttuple [tvar "c", tvar "a"] \-> ttuple [tvar "c", tvar "b"])
        it "infers function application" $ do
            inferExprString "(fun x -> x) ()" `shouldBe` Right tunit
            inferExprString "(fun x -> ()) ((),())" `shouldBe` Right tunit
        it "infers let" $ do
            inferExprString "let x = () in x" `shouldBe` Right tunit
            inferExprString "let id = (fun x -> x) in id" `shouldBe` Right (tvar "a" \-> tvar "a")
            inferExprString "let id = (fun x -> x) in id ()" `shouldBe` Right tunit
            inferExprString "let id = (fun x -> x) in id id" `shouldBe` Right (tvar "a" \-> tvar "a")
            inferExprString "let id = (fun x -> x) in (id id) ()" `shouldBe` Right tunit
        it "prevents calling non-functions" $ do
            inferExprString "() ()" `shouldBe` Left (Mismatch (tvar "a" \-> tvar "b") tunit)
        it "handles matches" $ do
            inferExprString "match () with | x -> x" `shouldBe` Right tunit
            inferExprString "match () with | () -> ()" `shouldBe` Right tunit
            inferExprString "match ((), ((), ())) with | (x,y) -> x" `shouldBe` Right tunit
            inferExprString "match ((), ((), ())) with | (x,y) -> y" `shouldBe` Right (ttuple [tunit, tunit])
            inferExprString "match ((), ((), ())) with | (x,(y,z)) -> y" `shouldBe` Right tunit
            inferExprString "match ((), ((), ())) with | (x,(y,z)) -> z" `shouldBe` Right tunit
            inferExprString "fun t -> match t with | (x,y) -> x" `shouldBe` Right (ttuple [tvar "a", tvar "b"] \-> tvar "a")
            inferExprString "let fst = fun t -> match t with | (x,y) -> x in fst" `shouldBe` Right (ttuple [tvar "a", tvar "b"] \-> tvar "a")
            inferExprString "let fst = fun t -> match t with | (x,y) -> x in fst ((), ((), ()))" `shouldBe` Right tunit
            inferExprString "let fst = fun t -> match t with | (x,y) -> x in fst (fst (((), ()), ()))" `shouldBe` Right tunit
        it "handles adts" $ do
            "type tt = TT;; let a = TT;;" `shouldProgInfer` Right [("a", tcon "tt" [])]
            "type tt = TT;; let a = match TT with TT -> ();;" `shouldProgInfer` Right [("a", tunit)]
            "type tt = TT;; let a = match TT with TT() -> ();;" `shouldProgInfer` Left (BadPConArity "TT" 0 1)
            "type 'a list = Empty | Cons of 'a * 'a list;; let a = Cons((),Empty);;" `shouldProgInfer` Right [("a", tlist tunit)]
            "type 'a list = Empty | Cons of 'a * 'a list;; let a = fun xs -> match xs with Cons(first,rest) -> first;;" `shouldProgInfer` Right [("a", tlist (tvar "a") \-> tvar "a")]
            "type 'a list = Empty | Cons of 'a * 'a list;; let a = fun xs -> match xs with Cons(first,rest) -> rest;;" `shouldProgInfer` Right [("a", tlist (tvar "a") \-> tlist (tvar "a"))]
            "type 'a list = Empty | Cons of 'a * 'a list;; let a = fun xs -> match xs with Cons(first,Cons(second,rest)) -> (first,second);;" `shouldProgInfer` Right [("a", tlist (tvar "a") \-> ttuple [tvar "a", tvar "a"])]
            "type 'a list = Empty | Cons of 'a * 'a list;; let a = fun xs -> match xs with Cons(first,Cons(second,rest)) -> (first,second);;" `shouldProgInfer` Right [("a", tlist (tvar "a") \-> ttuple [tvar "a", tvar "a"])]
            let prog = unlines
                    [ "type bool = True | False"
                    , "let not = fun b -> match b with True -> False | False -> True"
                    , "let and' = fun a b -> match (a,b) with (True,True) -> True | x -> False"
                    , "let or = fun a b -> not (and' (not a) (not b))"
                    ]
                expected = Right
                    [ ("not", tbool \-> tbool)
                    , ("and'", tbool \-> tbool \-> tbool)
                    , ("or", tbool \-> tbool \-> tbool)
                    ]
                in prog `shouldProgInfer` expected
            let prog = unlines
                    [ "type 'a list = Empty | Cons of 'a * 'a list"
                    , "type bool = True | False"
                    , "let not = fun b -> match b with True -> False | False -> True"
                    , "let and' = fun a b -> match (a,b) with (True,True) -> True | x -> False"
                    , "let or = fun a b -> not (and' (not a) (not b))"
                    , "let f = fun bs -> match bs with Cons(first,Cons(second,rest)) -> and' first second"
                    ]
                expected = Right
                    [ ("not", tbool \-> tbool)
                    , ("and'", tbool \-> tbool \-> tbool)
                    , ("or", tbool \-> tbool \-> tbool)
                    , ("f", tlist tbool \-> tbool)
                    ]
                in prog `shouldProgInfer` expected
            let prog = unlines
                    [ "type 'a list = Empty | Cons of 'a * 'a list"
                    , "let f = fun bs -> match bs with Cons((x,y),Cons(second,rest)) -> x"
                    ]
                expected = Right [("f", tlist (ttuple [tvar "a", tvar "b"]) \-> tvar "a")]
                in prog `shouldProgInfer` expected
        it "handles recursive functions" $ do
            inferExprString "let rec f = f in f" `shouldBe` Right (tvar "a")
            let prog = unlines
                    [ "type 'a list = Empty | Cons of 'a * 'a list"
                    , "let rec map = fun f xs -> match xs with"
                    , "  | Empty -> Empty"
                    , "  | Cons(x,xs') -> Cons(f x,map f xs')"
                    ]
                expected = Right [("map", (tvar "a" \-> tvar "b") \-> tlist (tvar "a") \-> tlist (tvar "b"))]
                in prog `shouldProgInfer` expected
            -- messed up map function
            let prog = unlines
                    [ "type 'a list = Empty | Cons of 'a * 'a list"
                    , "let rec map = fun f xs -> match xs with"
                    , "  | Empty -> Empty"
                    , "  | Cons(x,xs') -> Cons(f x,xs')" -- forget to recurse
                    ]
                expected = Right [("map", (tvar "a" \-> tvar "a") \-> tlist (tvar "a") \-> tlist (tvar "a"))]
                in prog `shouldProgInfer` expected
            let prog = stdTypes ++ unlines
                    [ "let rec odd = fun n -> match n with"
                    , "  | Zero -> False"
                    , "  | Succ n' -> even n'"
                    , "and even = fun n -> match n with"
                    , "  | Zero -> True"
                    , "  | Succ n' -> odd n'"
                    ]
                expected = Right
                    [("odd", tnat \-> tbool), ("even", tnat \-> tbool)]
                in prog `shouldProgInfer` expected
            let prog = stdTypes ++ unlines
                    [ "let rec zip = fun xs ys -> match (xs, ys) with"
                    , "  | (Empty,a) -> Empty"
                    , "  | (a,Empty) -> Empty"
                    , "  | (Cons(x,xs'),Cons(y,ys')) -> Cons((x,y),zip xs' ys')"
                    ]
                expected = Right [("zip", tlist (tvar "a") \-> tlist (tvar "b") \-> tlist (ttuple [tvar "a", tvar "b"]))]
                in prog `shouldProgInfer` expected
            -- bad zip
            let prog = stdTypes ++ unlines
                    [ "let rec zip = fun xs ys -> match (xs, ys) with"
                    , "  | (Empty,a) -> Empty"
                    , "  | (a,Empty) -> Empty"
                    , "  | (Cons(x,xs'),Cons(y,ys')) -> Cons((x,y),zip ys' xs')" -- swap xs' ys'
                    ]
                expected = Right [("zip", tlist (tvar "a") \-> tlist (tvar "a") \-> tlist (ttuple [tvar "a", tvar "a"]))]
                in prog `shouldProgInfer` expected
        it "prevents infinte types" $ do
            inferExprString "let rec f = fun x -> f in f" `shouldBe` Left (OccursError "a" (tvar "b" \-> tvar "a"))
            inferExprString "let rec f = fun x -> (x,f x) in f" `shouldBe` Left (OccursError "d" (ttuple [tvar "b",  tvar "d"]))
        it "handles conflicting rhs of match" $ do
            inferExprString "match () with a -> () | b -> ((),())" `shouldBe` Left (Mismatch tunit (ttuple [tunit,tunit]))
            inferExprString "fun x -> match x with a -> x | b -> ()" `shouldBe` Right (tunit \-> tunit)
            inferExprString "fun x -> match x with a -> () | b -> x" `shouldBe` Right (tunit \-> tunit)
            (stdTypes ++ "let f = fun x -> match x with True -> True | False -> Zero") `shouldProgInfer` Left (Mismatch tbool tnat)
            (stdTypes ++ "let f = fun x -> match x with True -> Cons(True,Empty) | False -> Cons(Zero,Empty)") `shouldProgInfer` Left (Mismatch tbool tnat)
        it "handles conflicting lhs of match" $ do
            (stdTypes ++ "let f = fun x -> match x with True -> True | Zero -> True") `shouldProgInfer` Left (Mismatch tbool tnat)
            (stdTypes ++ "let f = fun x -> match x with Cons(True,Empty) -> True | Cons(Zero,Empty) -> True") `shouldProgInfer` Left (Mismatch tbool tnat)
        it "handles bad constructor arity" $ do
            (stdTypes ++ "let x = True()") `shouldProgInfer` Left (Mismatch (tvar "a" \-> tvar "b") tbool)
            (stdTypes ++ "let x = match True with True() -> ()") `shouldProgInfer` Left (BadPConArity "True" 0 1)
            (stdTypes ++ "let x = match Empty with Cons -> ()") `shouldProgInfer` Left (BadPConArity "Cons" 1 0)
            (stdTypes ++ "let x = match Cons(True,Empty) with Cons x -> x") `shouldProgInfer` Right [("x", ttuple [tbool, tlist tbool])]
            (stdTypes ++ "type t = T of bool;; let x = match T True with T x -> x") `shouldProgInfer` Right [("x",tbool)]
            (stdTypes ++ "type t = T of bool;; let x = match T True with T(x) -> x") `shouldProgInfer` Right [("x",tbool)]
        it "instantiates on matches" $ do
            inferExprString "match (fun x -> x) with f -> f f ()" `shouldBe` Left (OccursError "a" (tvar "a" \-> tvar "a"))
            inferExprString "(fun x -> x) (fun x -> x) ()" `shouldBe` Right tunit
        it "doesn't allow y combinator :(" $ do
            inferExprString "fun f -> (fun x -> f (x x)) (fun x -> f (x x))" `shouldBe` Left (OccursError "g" (tvar "g" \-> tvar "h"))
        it "infers foldr" $ do
            let prog = stdTypes ++ unlines
                    [ "let rec foldr = fun f z xs -> match xs with"
                    , "  | Empty -> z"
                    , "  | Cons(x,xs) -> f x (foldr f z xs)"
                    , "let map = fun f -> foldr (fun x ys -> Cons(f x,ys)) Empty"
                    , "let flip = fun f x y -> f y x"
                    , "let curry = fun f x y -> f (x,y)"
                    , "let append = flip (foldr (curry Cons))"
                    , "let concat = foldr append Empty"
                    ]
                expected = Right
                    [ ("foldr", (tvar "a" \-> tvar "b" \-> tvar "b") \-> tvar "b" \-> tlist (tvar "a") \-> tvar "b")
                    , ("map", (tvar "a" \-> tvar "b") \-> tlist (tvar "a") \-> tlist (tvar "b"))
                    , ("append", tlist (tvar "a") \-> tlist (tvar "a") \-> tlist (tvar "a"))
                    , ("concat", tlist (tlist (tvar "a")) \-> tlist (tvar "a"))
                    ]
                in prog `shouldProgInfer` expected
        it "infers monadic bind" $ do
            let prog = unlines
                    [ "type 'a option = None | Some of 'a"
                    , "let bind = fun ma k -> match ma with"
                    , "  | None -> None"
                    , "  | Some a -> k a"
                    ]
                expected = Right
                    [ ("bind", toption (tvar "a") \-> (tvar "a" \-> toption (tvar "b")) \-> toption (tvar "b"))
                    ]
                in shouldProgInfer prog expected
            let prog = unlines
                    [ "type ('a,'b) result = Ok of 'a | Error of 'b"
                    , "let bind = fun ma k -> match ma with"
                    , "  | Error err -> Error err"
                    , "  | Ok a -> k a"
                    ]
                expected = Right
                    [ ("bind", tresult (tvar "a") (tvar "b") \-> (tvar "a" \-> tresult (tvar "c") (tvar "b")) \-> tresult (tvar "c") (tvar "b"))
                    ]
                in shouldProgInfer prog expected
            let prog = unlines
                    [ "type 'a list = Empty | Cons of 'a * 'a list"
                    , "let rec foldr = fun f z xs -> match xs with"
                    , "  | Empty -> z"
                    , "  | Cons(x,xs) -> f x (foldr f z xs)"
                    , "let map = fun f -> foldr (fun x ys -> Cons(f x,ys)) Empty"
                    , "let flip = fun f x y -> f y x"
                    , "let curry = fun f x y -> f (x,y)"
                    , "let append = flip (foldr (curry Cons))"
                    , "let concat = foldr append Empty"
                    , "let concatMap = fun f xs -> concat (map f xs)"
                    , "let bind = flip concatMap"
                    ]
                expected = Right
                    [ ("bind", tlist (tvar "a") \-> (tvar "a" \-> tlist (tvar "b")) \-> tlist (tvar "b"))
                    ]
                in shouldProgInfer prog expected
    describe "well formedness checker" $ do
        it "handles unbound vars" $ do
            wfExprString "x" `shouldBe` [WF.UnboundVar "x"]
            wfExprString "let x = x in ()" `shouldBe` [WF.UnboundVar "x"]
            wfExprString "let x = (let y = () in y) in y" `shouldBe` [WF.UnboundVar "y"]
            wfExprString "let rec x = x in x" `shouldBe` []
            wfExprString "match () with x -> (x,y)" `shouldBe` [WF.UnboundVar "y"]
            wfExprString "((((x),()),()),())" `shouldBe` [WF.UnboundVar "x"]
            wfExprString "X" `shouldBe` [WF.UnboundVar "X"]
        it "handles duplicates variables in let rec" $ do
            wfExprString "let rec x = () and x = () in ()" `shouldBe` [WF.DupVar "x"]
            wfExprString "let rec x = () and y = () and x = () in ()" `shouldBe` [WF.DupVar "x"]
            wfExprString "let rec x = (let rec x = x in x) in x" `shouldBe` []
            wfProgString "let rec x = () and x = ()" `shouldBe` [WF.DupVar "x"]
            wfProgString "let rec x = () and y = () and x = ()" `shouldBe` [WF.DupVar "x"]
            wfProgString "let rec x = (let rec x = x in x)" `shouldBe` []
            wfExprString "let x = () in let x = () in x" `shouldBe` []
            wfProgString "let x = ();; let x = ()" `shouldBe` []
        it "handles duplicate type definitions" $ do
            wfProgString "type bool = True;; type bool = True | False" `shouldBe` [WF.DupTCon "bool", WF.DupVar "True"]
            wfProgString "type bool = T;; let x = T;; type bool = True" `shouldBe` [WF.DupTCon "bool"]
            wfProgString "type bool = T;; let x = T;; type 'a bool = True" `shouldBe` [WF.DupTCon "bool"]
        it "handles duplicate constructor names" $ do
            wfProgString "type t = T | T" `shouldBe` [WF.DupVar "T"]
            wfProgString "type t = T;; type t2 = T" `shouldBe` [WF.DupVar "T"]
        it "handles duplicate type argument names to types" $ do
            wfProgString "type ('a, 'a) list = Empty" `shouldBe` [WF.DupTVar "a"]
            wfProgString "type ('a, 'b, 'a) list = Empty" `shouldBe` [WF.DupTVar "a"]
            wfProgString "type 'a list = Empty;; type 'a list2 = Empty2" `shouldBe` []
        it "allows recursive types" $ do
            wfProgString "type 'a list = Empty | Cons of 'a * 'a list" `shouldBe` []
            wfProgString "type 'a bt = Leaf of 'a | Node of 'a bt * 'a bt" `shouldBe` []
        it "handles unbound types in type definitions" $ do
            wfProgString "type t = T of t2" `shouldBe` [WF.UnboundTCon "t2"]
            wfProgString "type t = T of t2;; type t2 = T2" `shouldBe` [WF.UnboundTCon "t2"]
        it "handles unbound type variables in type definitions" $ do
            wfProgString "type t = T of 'a" `shouldBe` [WF.UnboundTVar "a"]
            wfProgString "type 'a list = Empty | Cons of 'a * 'a list;; type t = T of 'a list" `shouldBe` [WF.UnboundTVar "a"]
        it "handles patterns with duplicate variables" $ do
            wfExprString "match ((),()) with (x,x) -> x" `shouldBe` [WF.DupVar "x"]
            wfExprString "match ((),((),())) with (x,(x,y)) -> x" `shouldBe` [WF.DupVar "x"]
            wfExprString "match ((),()) with | (x,y) -> x | (x,y) -> y" `shouldBe` []
        it "handles type arity errors" $ do
            wfProgString "type t = T;; type 'a t' = T' of 'a t" `shouldBe` [WF.TypeArityError "t" 0 1]
            wfProgString "type 'a t = T;; type 'a t' = T' of t" `shouldBe` [WF.TypeArityError "t" 1 0]
            let prog = unlines
                    [ "type ('a,'b) pair = Pair of 'a * 'b"
                    , "type t0 = T0 of pair"
                    , "type 'a t1 = T1 of 'a pair"
                    , "type ('a,'b,'c) t3 = T3 of ('a,'b,'c) pair" 
                    ]
                errs = WF.TypeArityError "pair" 2 <$> [0,1,3]
                in wfProgString prog `shouldBe` errs
            
            
            
