{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}

module OCovid.Static.WellFormedness where

import Control.Monad.RWS.Strict

import OCovid.Syntax.Expr
import OCovid.Syntax.Program
import OCovid.Static.Types

import qualified Data.Map as Map
import Data.Map(Map)

import Control.Arrow ((>>>))
import Data.Function ((&))

-- TODO assert rhs of letrec is fun

-- types --

data WFError = UnboundVar String
             | UnboundTVar String
             | UnboundTCon String
             | TypeArityError String Int Int
             | DupVar String
             | DupTVar String
             | DupTCon String
             | InternalError String
               deriving(Eq, Ord, Show)

data Env = Env {getVars :: [String], getTVars :: [String], getTCons :: Map String Int} deriving(Eq, Ord, Show)

instance Semigroup Env where
    Env a b c <> Env a' b' c' = Env (a <> a') (b <> b') (c <> c')

instance Monoid Env where
    mempty = Env mempty mempty mempty

emptyEnv :: Env
emptyEnv = mempty

newtype Checker a = Checker { runChecker :: (RWS Env [WFError] ()) a }
    deriving( Functor
            , Applicative
            , Monad
            , MonadReader Env
            , MonadWriter [WFError]
            )

-- utility --

throwError :: WFError -> Checker ()
throwError e = tell [e]

nothing :: Monad m => m ()
nothing = return ()

withVar :: String -> Checker a -> Checker a
withVar v = local (\e -> e{getVars=v:getVars e})

withVars :: [String] -> Checker a -> Checker a
withVars vs = local (\e -> e{getVars=vs++getVars e})

withTVars :: [String] -> Checker a -> Checker a
withTVars vs = local (\e -> e{getTVars=vs++getTVars e})

withTCon :: String -> Int -> Checker a -> Checker a
withTCon c arity = local (\e -> e{getTCons=Map.insert c arity $ getTCons e})

assertVar :: String -> Checker ()
assertVar x = do
    exists <- asks (\e -> x `elem` getVars e)
    unless exists (throwError (UnboundVar x))

assertTVar :: String -> Checker ()
assertTVar x = do
    exists <- asks (\e -> x `elem` getTVars e)
    unless exists (throwError (UnboundTVar x))

assertTCon :: String -> Checker ()
assertTCon x = do
    exists <- asks (\e -> x `Map.member` getTCons e)
    unless exists (throwError (UnboundTCon x))

assertTConArity :: String -> Int -> Checker ()
assertTConArity c actualArity = do
    e <- ask
    case Map.lookup c (getTCons e) of
        Nothing -> throwError (UnboundTCon c)
        Just expectedArity ->
            unless (expectedArity == actualArity) (throwError (TypeArityError c expectedArity actualArity))

checkDups :: (String -> WFError) -> [String] -> Checker ()
checkDups onDup = reverse >>> go >>> reverse >>> tell
    where go [] = []
          go (x:xs)
            | x `elem` xs = onDup x:go xs
            | otherwise = go xs

checkDupVar :: [String] -> Checker ()
checkDupVar = checkDups DupVar

checkDupTVar :: [String] -> Checker ()
checkDupTVar = checkDups DupTVar

checkDupTCon :: [String] -> Checker ()
checkDupTCon = checkDups DupTCon


-- checking --

checkCase :: Pattern -> Expr -> Checker ()
checkCase p rhs = do
    let -- | does not remove duplicates
        freePatternVarsDups :: Pattern -> [String]
        freePatternVarsDups = \case
            PVar x -> [x]
            PTuple ps -> (concatMap freePatternVarsDups ps)
            PCon _ mP -> maybe [] freePatternVarsDups mP
    let vars = freePatternVarsDups p
    checkPattern p
    checkDupVar vars
    withVars vars (checkExpr rhs)

checkExpr :: Expr -> Checker ()
checkExpr = \case
    Var x -> assertVar x
    App f x -> checkExpr f >> checkExpr x
    Tuple es -> mapM_ checkExpr es
    Fun args e -> withVars args (checkExpr e)
    Let x rhs body -> checkExpr rhs >> withVar x (checkExpr body)
    LetRec bindings body -> do
        let (vars, rhss) = unzip bindings
        checkDupVar vars
        mapM_ (withVars vars . checkExpr) (rhss++[body])
    Match target cases -> do
        checkExpr target
        mapM_ (uncurry checkCase) cases
    Con c -> assertVar c

checkPattern :: Pattern -> Checker ()
checkPattern = \case
    PVar{} -> nothing
    PTuple ps -> mapM_ checkPattern ps
    PCon c mP -> assertVar c >> maybe nothing checkPattern mP

checkType :: Type -> Checker ()
checkType = \case
    TVar x -> assertTVar x
    TArr arg ret -> checkType arg >> checkType ret
    TTuple ts -> mapM_ checkType ts
    TCon c args -> do
        assertTConArity c (length args)
        mapM_ checkType args

checkTopDecls :: [TopDecl] -> Checker ()
checkTopDecls decls =
    checkDupTCon (concatMap getType decls)
    >> checkDupVar (concatMap getConstructors decls)
    >> go decls
    where
        getType = \case
            TyDecl _ name _ -> [name]
            LetDecl{} -> []
            LetRecDecl{} -> []
        getConstructors = \case
            TyDecl _ _ cases -> fmap fst cases
            LetDecl{} -> []
            LetRecDecl{} -> []
        go [] = nothing
        go (decl:rest) = let mRest = go rest in case decl of
            LetDecl x rhs -> checkExpr rhs >> withVar x mRest
            LetRecDecl bindings -> do
                let (vars, rhss) = unzip bindings
                checkDupVar vars
                mapM_ (withVars vars . checkExpr) rhss
                withVars vars mRest
            TyDecl targs name cases -> do
                let (cons, mTs) = unzip cases
                    arity = length targs
                checkDupTVar targs
--                checkDupVar cons -- this is already done in its own pass
                withTCon name arity . withTVars targs $ mapM_ (maybe nothing checkType) mTs
                withTCon name arity . withVars cons $ mRest

checkProgram :: Program -> Checker ()
checkProgram (Program decls) = checkTopDecls decls

-- running the monad --

executeChecker :: Checker a -> [WFError]
executeChecker c =
    c
    & runChecker
    & \m -> runRWS m mempty ()
    & (\(_,_,x) -> x)

checkProgramWellFormedness :: Program -> Either [WFError] Program
checkProgramWellFormedness p = case executeChecker . checkProgram $ p of
    [] -> Right p
    errs -> Left errs



