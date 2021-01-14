module OCovid.Syntax.Pattern where

data Pattern = PVar String
             | PTuple [Pattern]
             deriving(Eq, Ord, Show)