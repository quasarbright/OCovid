module OCovid.Syntax.Expr where

import OCovid.Syntax.Pattern

data Expr = Var String
          | App Expr Expr
          | Tuple [Expr]
          | Fun [String] Expr
          | Let String Expr Expr
          | Match Expr [(Pattern, Expr)]
          deriving(Eq, Ord, Show)