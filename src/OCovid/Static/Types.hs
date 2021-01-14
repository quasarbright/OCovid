module OCovid.Static.Types where

import Data.List (intercalate, nub)

data Type = TVar String
          | TArr Type Type
          | TTuple [Type] deriving (Eq, Ord)

instance Show Type where
    show (TVar x) = x
    show (TArr arg ret) = "("++show arg++"->"++show ret++")"
    show (TTuple []) = "unit"
    show (TTuple ts) = "("++intercalate " * " (show <$> ts)++")"

data Scheme = SForall String Scheme
            | SMono Type
            deriving(Eq, Ord, Show)

freeVars :: Scheme -> [String]
freeVars (SForall x t) = nub (filter (/= x) (freeVars t))
freeVars (SMono t') = go t'
    where go t = case t of
                    TVar x -> [x]
                    TArr arg ret -> nub (go arg ++ go ret)
                    TTuple ts -> nub (ts >>= go)