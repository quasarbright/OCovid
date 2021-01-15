{-# LANGUAGE LambdaCase #-}

module OCovid.Syntax.Expr where

import OCovid.Syntax.Pattern

data Expr = Var String
          | App Expr Expr
          | Tuple [Expr]
          | Fun [String] Expr
          | Let String Expr Expr
          | Match Expr [(Pattern, Expr)]
          deriving(Eq, Ord, Show)

data Pattern = PVar String
             | PTuple [Pattern]
             deriving(Eq, Ord, Show)

exprOfPattern :: Pattern -> Expr
exprOfPattern = \case
    PVar x -> Var x
    PTuple ps -> Tuple (fmap exprOfPattern ps)

patternOfExpr :: Expr -> Maybe Pattern
patternOfExpr = \case
    Var x -> Just $ PVar x
    App{} -> Nothing
    Tuple es -> PTuple <$> mapM patternOfExpr es
    Fun{} -> Nothing
    Let{} -> Nothing
    Match{} -> Nothing