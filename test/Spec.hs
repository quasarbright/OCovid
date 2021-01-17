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
            