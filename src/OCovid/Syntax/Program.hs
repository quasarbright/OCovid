module OCovid.Syntax.Program where

import OCovid.Syntax.Expr
import OCovid.Static.Types

-- type 'a list = Empty | Cons of 'a * 'a list

data TopDecl = LetDecl String Expr
             | LetRecDecl [(String,Expr)]
             | TyDecl [String] String [(String, Maybe Type)]
             deriving(Eq, Ord, Show)

newtype Program = Program [TopDecl] deriving (Eq, Ord, Show)