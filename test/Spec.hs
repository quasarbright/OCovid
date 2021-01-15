import Test.Hspec

import OCovid.Parsing.Parse
import OCovid.Syntax.Expr
import OCovid.Syntax.Program
import OCovid.Static.Types

import OCovid.Static.Typing

inferExprString :: String -> Either TypeError Type
inferExprString src = case parseExpr "test/Spec.hs" src of
    Left err -> Left (InternalError err)
    Right e -> case inferAndFinalizeExpr e of
        Left err -> Left err
        Right t -> Right (simplifyMono t)

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
            inferExprString "fun f g x -> f (g x)" `shouldBe` Right ((tvar "a" \-> tvar "b") \-> (tvar "c" \-> tvar "a") \-> tvar "c" \-> tvar "b")
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
