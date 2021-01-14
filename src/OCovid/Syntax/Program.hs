module OCovid.Syntax.Program where

import OCovid.Syntax.Expr

newtype Program = Program [(String, Expr)] deriving (Eq, Ord, Show)