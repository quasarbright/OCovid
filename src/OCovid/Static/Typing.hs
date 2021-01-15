{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module OCovid.Static.Typing where

import OCovid.Static.Types
import OCovid.Util.UnionFind
import Control.Monad.RWS.Strict
import Control.Monad.Except

import qualified Data.Set as Set
import Data.Set(Set)

import Data.Map(Map)
import qualified Data.Map as Map
import Control.Arrow ((>>>))

import OCovid.Syntax.Expr
import OCovid.Syntax.Program
import Data.Function ((&))

-- types --

data TypeError = Mismatch Type Type
               | OccursError String Type
               | UnboundVar String
               | InternalError String
               deriving(Eq, Ord, Show)

type Store = (UnionFind Type, [String])

emptyStore :: Store
emptyStore = (mempty, names)

type Env = Map String Scheme

emptyEnv :: Env
emptyEnv = mempty

newtype Checker a = Checker { runChecker :: ExceptT TypeError (RWS Env () Store) a }
    deriving( Functor
            , Applicative
            , Monad
            , MonadState Store
            , MonadReader Env
            , MonadError TypeError
            )

-- utility --

freeEnvVars :: Map String Scheme -> Set String
freeEnvVars = Map.toList >>> fmap (snd >>> freeSchemeVars) >>> Set.unions

getUF :: Checker (UnionFind Type)
getUF = gets fst

modUF :: (UnionFind Type -> UnionFind Type) -> Checker ()
modUF f = do
    (uf,ns) <- get
    put (f uf,ns)

getNS :: Checker [String]
getNS = gets snd

modNS :: ([String] -> [String]) -> Checker ()
modNS f = do
    (uf, ns) <- get
    put (uf, f ns)

unify :: Type -> Type -> Checker ()
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
            | x `elem` freeMonoVars t -> throwError (OccursError x t)
            | otherwise -> modUF $ const (union uf t2' t1')
        (t, TVar x)
            | x `elem` freeMonoVars t -> throwError (OccursError x t)
            | otherwise -> modUF $ const (union uf t1' t2')
        (TArr{}, _) -> throwError (Mismatch t1' t2')
        (TTuple{}, _) -> throwError (Mismatch t1' t2')

shortlex :: [a] -> [[a]]
shortlex xs = [[x] | x <- xs] ++ [xs' ++ [x] | xs' <- shortlex xs, x <- xs]

names :: [[Char]]
names = shortlex ['a'..'z']

freshName :: Checker String
freshName = do
    ns <- getNS
    let n = head ns
    let ns' = tail ns
    modNS (const ns')
    return n

freshNames :: Integral a => a -> Checker [String]
freshNames 0 = return []
freshNames n = liftM2 (:) freshName (freshNames (pred n))

lookupVar :: String -> Checker Scheme
lookupVar x = do
    mT <- asks (Map.lookup x)
    case mT of
        Nothing -> throwError (UnboundVar x)
        Just t -> return t

annot :: String -> Scheme -> Checker a -> Checker a
annot x t = local (Map.insert x t)

annots :: [(String, Scheme)] -> Checker a -> Checker a
annots vars = local $ \m -> foldr (uncurry Map.insert) m vars

annotsMap :: Map String Scheme -> Checker a -> Checker a
annotsMap vars = local $ Map.union vars

findMono :: Type -> Checker Type
findMono t = case t of
    TVar{} -> do
        uf <- getUF
        return (find uf t)
    TArr arg ret -> TArr <$> findMono arg <*> findMono ret
    TTuple ts -> TTuple <$> mapM findMono ts

-- | simplify the type variables so gd -> ddf appears as a -> b
simplifyMono :: Type -> Type
simplifyMono t =
    let frees = freeMonoVarsOrdered t
        n = length frees
        -- this is necessary bc if frees is [b,a], replacements is [(a->b,b->a)], you get all bs
        -- if you made a map substitution function, this wouldn't be necessary
        names_ = show <$> ([1..] :: [Int])
        replacements = zip frees (fmap TVar names_)
        t' = subs subMono replacements t
        replacements' = zip (take n names_) (fmap TVar names)
        t'' = subs subMono replacements' t'
    in t''

finalizeScheme :: Scheme -> Checker Scheme
finalizeScheme = instantiate >=> finalizeMono

finalizeMono :: Type -> Checker Scheme
finalizeMono = findMono >=> (return . simplifyMono) >=> (return . blindGeneralize)

-- inference --

-- | make a mono type of a scheme using fresh type variables
instantiate :: Scheme -> Checker Type
instantiate = \case
    SForall x t -> do
        x' <- freshName
        instantiate (subScheme x (TVar x') t)
    SMono t -> do
        return t

-- | make a scheme of a mono type by escaping free type variables
generalize :: Type -> Checker Scheme
generalize t_ = do
    t <- findMono t_
    envFrees <- asks freeEnvVars
    let monoFrees = freeMonoVars t
        frees = monoFrees `Set.difference` envFrees & Set.toList
    return (foldr SForall (SMono t) frees)

inferExpr :: Expr -> Checker Type
inferExpr = \case
    Var x -> instantiate =<< lookupVar x
    App f x -> do
        arg <- fmap TVar freshName
        ret <- fmap TVar freshName
        checkExpr (TArr arg ret) f
        checkExpr arg x
        return ret
    Tuple es -> TTuple <$> mapM inferExpr es
    Fun args body -> do
        taus <- freshNames (length args)
        let argSchemes = SMono . TVar <$> taus
        tBody <- annots (zip args argSchemes) (inferExpr body)
        return $ foldr TArr tBody (fmap TVar taus)
    Let x rhs body -> do
        tRhs <- inferExpr rhs
        tRhs' <- generalize tRhs
        annot x tRhs' (inferExpr body)
    Match e cases -> do
        tE <- inferExpr e
        ts <- mapM (uncurry (inferMatchCase tE)) cases
        zipWithM_ unify ts (tail ts)
        return $ head ts

checkExpr :: Type -> Expr -> Checker ()
checkExpr t e = unify t =<< inferExpr e

inferMatchCase :: Type -> Pattern -> Expr -> Checker Type
inferMatchCase t p rhs = do
    vars <- checkPattern t p
    let varsPairs = Map.toList vars
    varsPairsGen <- mapM (\(x,t') -> (x,) <$> (SMono <$> findMono t')) varsPairs
    annots varsPairsGen (inferExpr rhs)

checkPattern :: Type -> Pattern -> Checker (Map String Type)
checkPattern t = \case
    PVar x -> return $ Map.singleton x t -- TODO should you find here?
    PTuple ps -> do
        ts <- fmap TVar <$> freshNames (length ps)
        let t' = TTuple ts
        unify t t'
        maps <- zipWithM checkPattern ts ps
        return $ Map.unions maps


-- | type check the program and return the mapping from names to types of
-- top level variables
checkProgram :: Program -> Checker Env
checkProgram (Program bindings) = go bindings
    where
        go [] = ask
        go ((x,rhs):rest) = do
            tRhs <- inferExpr rhs
            tRhs' <- finalizeScheme =<< generalize tRhs
            annot x tRhs' (go rest)

-- running the monads --

executeChecker :: Checker a -> Either TypeError a
executeChecker =
    runChecker
    >>> runExceptT
    >>> (\m -> runRWS m emptyEnv emptyStore)
    >>> (\(a,_,_) -> a)

inferAndFinalizeExpr :: Expr -> Either TypeError Type
inferAndFinalizeExpr e = executeChecker (inferExpr e >>= finalizeMono >>= (return . blindInstantiate))