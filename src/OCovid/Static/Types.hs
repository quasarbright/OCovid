{-# LANGUAGE LambdaCase #-}

module OCovid.Static.Types where

import Data.List (intercalate, nub)
import qualified Data.Set as Set
import Data.Set(Set)

data Type = TVar String
          | TArr Type Type
          | TTuple [Type]
          | TCon String [Type]
          deriving (Eq, Ord)

tunit :: Type
tunit = TTuple []

infixr 5 \->
(\->) :: Type -> Type -> Type
(\->) = TArr

tvar :: String -> Type
tvar = TVar

ttuple :: [Type] -> Type
ttuple = TTuple

tcon :: String -> [Type] -> Type
tcon = TCon

tlist :: Type -> Type
tlist t = TCon "list" [t]

tbool :: Type
tbool = TCon "bool" []

instance Show Type where
    show (TVar x) = "'"++x
    show (TArr arg ret) = "("++show arg++"->"++show ret++")"
    show (TTuple []) = "unit"
    show (TTuple ts) = "("++intercalate " * " (show <$> ts)++")"
    show (TCon name [arg]) = show arg ++ " " ++ name
    show (TCon name args) = "("++intercalate ", " (show <$> args)++") "++name

data Scheme = SForall String Scheme
            | SMono Type
            deriving(Eq, Ord, Show)

freeSchemeVars :: Scheme -> Set String
freeSchemeVars (SForall x t) = Set.delete x $ freeSchemeVars t
freeSchemeVars (SMono t) = freeMonoVars t

freeMonoVars :: Type -> Set String
freeMonoVars = \case
    TVar x -> Set.singleton x
    TArr arg ret -> freeMonoVars arg `Set.union` freeMonoVars ret
    TTuple ts -> Set.unions (fmap freeMonoVars ts)
    TCon _ args -> Set.unions (fmap freeMonoVars args)

freeMonoVarsOrdered :: Type -> [String]
freeMonoVarsOrdered = \case
    TVar x -> [x]
    TArr arg ret -> nub (freeMonoVarsOrdered arg++freeMonoVarsOrdered ret)
    TTuple ts -> nub (freeMonoVarsOrdered =<< ts)
    TCon _ args -> nub (freeMonoVarsOrdered =<< args)
    

subMono :: String -> Type -> Type -> Type
subMono target replacement = let go = subMono target replacement in \case
    TVar x | x == target -> replacement
           | otherwise -> TVar x
    TArr arg ret -> TArr (go arg) (go ret)
    TTuple ts -> TTuple (fmap go ts)
    TCon name args -> TCon name (fmap go args)

subScheme :: String -> Type -> Scheme -> Scheme
subScheme target replacement = let go = subScheme target replacement in \case
    SForall x t | target == x -> SForall x t
                | otherwise -> SForall x (go t)
    SMono t -> SMono $ subMono target replacement t

-- | run the given substitution function with the list of replacements.
-- replacement order matters
subs :: Foldable t => (String -> Type -> a -> a) -> t (String, Type) -> a -> a
subs f replacements a = foldr (uncurry f) a replacements

blindGeneralize :: Type -> Scheme
blindGeneralize t = foldr SForall (SMono t) (freeMonoVars t)

blindInstantiate :: Scheme -> Type
blindInstantiate = \case
    SForall _ t -> blindInstantiate t
    SMono t -> t