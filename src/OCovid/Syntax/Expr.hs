{-# LANGUAGE LambdaCase #-}

module OCovid.Syntax.Expr where

data Expr = Var String
          | App Expr Expr
          | Tuple [Expr]
          | Fun [String] Expr
          | Let String Expr Expr
          | LetRec [(String,Expr)] Expr
          | Match Expr [(Pattern, Expr)]
          | Con String
          deriving(Eq, Ord, Show)

data Pattern = PVar String
             | PTuple [Pattern]
             | PCon String (Maybe Pattern)
             deriving(Eq, Ord, Show)

exprOfPattern :: Pattern -> Expr
exprOfPattern = \case
    PVar x -> Var x
    PTuple ps -> Tuple (fmap exprOfPattern ps)
    PCon c Nothing -> Con c
    PCon c (Just p) -> App (Con c) (exprOfPattern p)

patternOfExpr :: Expr -> Maybe Pattern
patternOfExpr = \case
    Var x -> Just $ PVar x
    App (Con c) e -> PCon c . Just <$> patternOfExpr e
    App{} -> Nothing
    Tuple es -> PTuple <$> mapM patternOfExpr es
    Fun{} -> Nothing
    Let{} -> Nothing
    Match{} -> Nothing
    Con c -> Just $ PCon c Nothing
    LetRec{} -> Nothing