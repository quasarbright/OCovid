{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module OCovid.Static.Typing where

import OCovid.Static.Types
import OCovid.Util.UnionFind
import Control.Monad.RWS.Strict
import Control.Monad.Except

import Data.Map(Map)
import qualified Data.Map as Map

data TypeError = Mismatch Type Type
               | OccursError String Type
               deriving(Eq, Ord, Show)

type Store = (UnionFind Type, [String])
type Env = Map String Scheme

newtype TypeChecker a = TypeChecker { runTypeChecker :: ExceptT TypeError (RWS Env () Store) a }
    deriving( Functor
            , Applicative
            , Monad
            , MonadState Store
            , MonadReader Env
            , MonadError TypeError
            )

getUF :: TypeChecker (UnionFind Type)
getUF = gets fst

modUF :: (UnionFind Type -> UnionFind Type) -> TypeChecker ()
modUF f = do
    (uf,ns) <- get
    put (f uf,ns)

getNS :: TypeChecker [String]
getNS = gets snd

modNS f = do
    (uf, ns) <- get
    put (uf, f ns)

unify :: Type -> Type -> TypeChecker ()
unify t1 t2 = do
    uf <- getUF
    let t1' = find uf t1
        t2' = find uf t2
    case (t1', t2') of
        (TArr arg1 ret1, TArr arg2 ret2) ->
            zipWithM_ unify [arg1, ret1] [arg2, ret2]
        (TTuple ts1, TTuple ts2)
            | length ts1 == length ts2 ->
                zipWithM_ unify ts1 ts2
            | otherwise -> throwError (Mismatch t1' t2')
        (TVar x, t)
            | x `elem` freeVars (SMono t) -> throwError (OccursError x t)
            | otherwise -> modUF $ const (union uf t2' t1')
        (t, TVar x)
            | x `elem` freeVars (SMono t) -> throwError (OccursError x t)
            | otherwise -> modUF $ const (union uf t1' t2')
        (TArr{}, _) -> throwError (Mismatch t1' t2')
        (TTuple{}, _) -> throwError (Mismatch t1' t2')

shortlex :: [a] -> [[a]]
shortlex xs = [[x] | x <- xs] ++ [xs' ++ [x] | xs' <- shortlex xs, x <- xs]

names :: [[Char]]
names = shortlex ['a'..'z']

freshName :: TypeChecker String
freshName = do
    ns <- getNS
    let n = head ns
    let ns' = tail ns
    modNS (const ns')
    reutrn n