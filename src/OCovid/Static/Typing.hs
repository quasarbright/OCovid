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
import Data.Tuple.Extra (secondM)

-- types --

data TypeError = Mismatch Type Type
               | OccursError String Type
               | UnboundVar String
               | InternalError String
               | BadPConArity String Int Int
               deriving(Eq, Ord, Show)

-- | maps ADTs to their type params and cases
type TyCons = Map String ([String], [(String, Maybe Type)])

type Store = (UnionFind Type, [String], TyCons)

emptyStore :: Store
emptyStore = (mempty, names, mempty)

type Env = Map String Scheme -- maps variables and constructors to types

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
getUF = gets (\(uf,_,_) -> uf)

modUF :: (UnionFind Type -> UnionFind Type) -> Checker ()
modUF f = do
    (uf,ns,tcm) <- get
    put (f uf,ns, tcm)

getNS :: Checker [String]
getNS = gets (\(_,ns,_) -> ns)

modNS :: ([String] -> [String]) -> Checker ()
modNS f = do
    (uf, ns, tcm) <- get
    put (uf, f ns, tcm)

getTCM :: Checker TyCons
getTCM = gets (\(_,_,tcm) -> tcm)

modTCM :: (TyCons -> TyCons) -> Checker ()
modTCM f = do
    (uf,ns,tcm) <- get
    put (uf, ns, f tcm)

addTyCon :: [String] -> String -> [(String, Maybe Type)] -> Checker ()
addTyCon args name cases = do
    modTCM (Map.insert name (args, cases))

getTyConInfo :: String -> Checker ([String], [(String, Maybe Type)])
getTyConInfo name = do
    tcm <- getTCM
    case Map.lookup name tcm of
        Nothing -> throwError (UnboundVar name)
        Just info -> return info

getTyConOfCon :: String -> Checker String
getTyConOfCon con = do
    tCon <- inferExpr (Con con)
    let getTCon (TArr _ t) = getTCon t
        getTCon t = t
    case getTCon tCon of
        TCon s _ -> return s
        _ -> throwError (InternalError "expected TCon")
    

unify :: Type -> Type -> Checker ()
unify t1 t2 = do
    uf <- getUF
    let t1' = find uf t1
        t2' = find uf t2
    case (t1', t2') of
        (TArr arg1 ret1, TArr arg2 ret2) ->
            zipWithM_ unify [arg1, ret1] [arg2, ret2]
        (TTuple ts1, TTuple ts2)
            | length ts1 == length ts2 -> zipWithM_ unify ts1 ts2
        (TCon name args, TCon name' args')
            | (name,length args) == (name', length args') -> zipWithM_ unify args args'
        (TVar x, t)
            | x `elem` freeMonoVars t -> throwError (OccursError x t)
            | otherwise -> modUF $ const (union uf t2' t1')
        (t, TVar x)
            | x `elem` freeMonoVars t -> throwError (OccursError x t)
            | otherwise -> modUF $ const (union uf t1' t2')
        (TArr{}, _) -> throwError (Mismatch t1' t2')
        (TTuple{}, _) -> throwError (Mismatch t1' t2')
        (TCon{}, _) -> throwError (Mismatch t1' t2')

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
        let t' = find uf t
        if t == t' then return t' else findMono t'
    TArr arg ret -> TArr <$> findMono arg <*> findMono ret
    TTuple ts -> TTuple <$> mapM findMono ts
    TCon name args -> TCon name <$> mapM findMono args

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
    Con c -> instantiate =<< lookupVar c

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
    PCon con mP -> do
        tycon <- getTyConOfCon con
        (argnames, cases) <- getTyConInfo tycon
        argts <- fmap TVar <$> freshNames (length argnames)
        let t' = TCon tycon argts
        unify t t'
        let replacements = zip argnames argts
        case lookup con cases of
            Nothing -> throwError (UnboundVar con)
            Just tCon -> case (tCon, mP) of
                -- constructors either expect a tuple type or nothing
                -- maybe constructor arg type vs maybe arg pattern
                (Nothing,Nothing) -> return mempty
                (Just argT, Just p) -> checkPattern (subs subMono replacements argT) p
                (Nothing, Just{}) -> throwError (BadPConArity con 0 1)
                (Just{}, Nothing) -> throwError (BadPConArity con 1 0)

checkTopDecls :: [TopDecl] -> Checker Env
checkTopDecls [] = ask
checkTopDecls (decl:rest) =
    let mRest = checkTopDecls rest
    in case decl of
        LetDecl x rhs -> do
            tRhs <- inferExpr rhs
            tRhs' <- finalizeScheme =<< generalize tRhs
            annot x tRhs' mRest
        TyDecl args name cases -> do
            -- register the adt
            addTyCon args name cases
            -- put the constructors in scope
            let go conName Nothing = (conName, blindGeneralize $ TCon name (fmap TVar args))
                go conName (Just t) = (conName, blindGeneralize $ t \-> TCon name (fmap TVar args))
                vars = fmap (uncurry go) cases
            annots vars mRest

-- | type check the program and return the mapping from names to types of
-- top level variables
checkProgram :: Program -> Checker Env
checkProgram (Program decls) = checkTopDecls decls

-- running the monads --

executeChecker :: Checker a -> Either TypeError a
executeChecker =
    runChecker
    >>> runExceptT
    >>> (\m -> runRWS m emptyEnv emptyStore)
    >>> (\(a,_,_) -> a)

executeChecker_ :: Checker a -> (Either TypeError a, UnionFind Type, TyCons)
executeChecker_ =
    runChecker
    >>> runExceptT
    >>> (\m -> runRWS m emptyEnv emptyStore)
    >>> (\(a,(uf,_,tcm),_) -> (a,uf,tcm))

inferAndFinalizeExpr :: Expr -> Either TypeError Type
inferAndFinalizeExpr e = executeChecker (inferExpr e >>= finalizeMono >>= (return . blindInstantiate))

typeCheckProgram :: Program -> Either TypeError (Map String Scheme)
typeCheckProgram p = executeChecker $ do
    m <- Map.toList <$> checkProgram p
    m' <- mapM (secondM finalizeScheme) m
    return (Map.fromList m')
            