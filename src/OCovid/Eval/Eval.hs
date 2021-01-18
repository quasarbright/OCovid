{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module OCovid.Eval.Eval where

import Control.Monad.RWS.Strict
import Control.Monad.Except

import OCovid.Syntax.Expr
import OCovid.Syntax.Program

import Data.Map(Map)
import qualified Data.Map as Map
import Control.Arrow ((>>>))
import Data.List (intercalate)

-- types --

data RuntimeError = PatternMatchFail
                  | InternalError String
                  | UnboundVar String
                  | UnboundAddr Addr
                  deriving(Eq, Ord, Show)

-- | heap things. complex structures
data Boxed = BFun String Expr Stack -- a function has the variables it closes over
           | BFunBuiltin (Cell -> Interpreter Cell)
           | BCon String (Maybe Cell)
           | BTuple [Cell]
           | BNull -- for letrec

-- | primitives/pointers. like a word of memory
newtype Cell = CPtr Addr
             -- primitives will go here
             deriving(Eq, Ord, Show)

data Value = VFun String Expr Stack
           | VFunBuiltin
           | VCon String (Maybe Value)
           | VTuple [Value]
           -- primitives will go here
           deriving(Eq, Ord)

instance Show Value where
    show = \case
        VFun x _ _ -> "<function "++x++">"
        VFunBuiltin -> "<builtin function>"
        VCon con Nothing -> con
        VCon con (Just v) -> con++" "++show v
        VTuple vs -> "("++intercalate ", " (show <$> vs)++")"

type Addr = Integer

type Heap = Map Addr Boxed

data Store = Store { storeHeap :: Heap, storeAddr :: Addr }

type Stack = Map String Cell

type Env = Stack

emptyEnv :: Env
emptyEnv = mempty

emptyStore :: Store
emptyStore = Store mempty 0

newtype Interpreter a = Interpreter { runInterpreter :: ExceptT RuntimeError (RWS Env () Store) a }
    deriving( Functor
            , Applicative
            , Monad
            , MonadReader Env
            , MonadState Store
            , MonadError RuntimeError
            )

-- utility --
getHeap :: Interpreter Heap
getHeap = gets storeHeap

modHeap :: (Heap -> Heap) -> Interpreter ()
modHeap f = modify $ \s -> s{storeHeap = f (storeHeap s)}

nextAddr :: Interpreter Addr
nextAddr = do
    Store heap addr <- get
    put $ Store heap (succ addr)
    return addr

getStack :: Interpreter Stack
getStack = ask

cellOfVar :: String -> Interpreter Cell
cellOfVar x = do
    stack <- getStack
    case Map.lookup x stack of
        Nothing -> throwError (UnboundVar x)
        Just cell -> return cell

boxedOfAddr :: Addr -> Interpreter Boxed
boxedOfAddr addr = do
    heap <- getHeap
    case Map.lookup addr heap of
        Nothing -> throwError (UnboundAddr addr)
        Just val -> return val

heapInsert :: Addr -> Boxed -> Interpreter ()
heapInsert addr boxed = modHeap $ Map.insert addr boxed

-- | stores the boxed value in the heap and returns its location
malloc :: Boxed -> Interpreter Addr
malloc boxed = do
    addr <- nextAddr
    heapInsert addr boxed
    return addr

withVar :: String -> Cell -> Interpreter a -> Interpreter a
withVar x c = local (Map.insert x c)

withVars :: [(String, Cell)] -> Interpreter a -> Interpreter a
withVars vars = local (mappend (Map.fromList vars))

-- | adds to the stack
withStack :: Stack -> Interpreter a -> Interpreter a
withStack vars = local (mappend vars)

-- | replaces the stack
usingStack :: Stack -> Interpreter a -> Interpreter a
usingStack = local . const

-- interpreter --

evalFun :: Stack -> [String] -> Expr -> Interpreter Boxed
evalFun stack [x] body = return $ BFun x body stack
evalFun stack (x:xs) body = evalFun stack [x] (Fun xs body)
evalFun _ [] _ = throwError (InternalError "tried to curry 0 argument function")

-- | runs the recursive bindings and returns a stack that includes them.
-- Creates null pointers for each variable, says each var points to null in stack,
-- includes those variables in stack for rhss,
-- evaluates fun boxes, fixes heap to make pointers point to fun boxes.
-- Since functions don't get evaluated until called, this null-and-patch works.
evalRecBindings :: [(String,Expr)] -> Interpreter Stack
evalRecBindings bindings = do
    let n = length bindings
        (vars, rhss) = unzip bindings
    addrs <- replicateM n (malloc BNull)
    stack <- getStack
    let stackAdds = zip vars (fmap CPtr addrs)
        -- includes bindings (currently point to null)
        stack' = Map.fromList stackAdds <> stack
        getFun :: Expr -> Interpreter ([String],Expr)
        getFun = \case
            Fun xs body' -> return (xs,body')
            _ -> throwError $ InternalError "expected function on rhs of letrec"
    funs <- mapM getFun rhss
    boxes <- mapM (uncurry (evalFun stack')) funs
    -- patch up null pointers
    zipWithM_ heapInsert addrs boxes
    return stack'

evalExpr :: Expr -> Interpreter Cell
evalExpr = \case
    Var x -> cellOfVar x
    App (Con c) e -> do
        eC <- evalExpr e
        CPtr <$> malloc (BCon c (Just eC))
    App f x -> do
        evalExpr f >>= \case
            CPtr addr -> do
                boxedOfAddr addr >>= \case
                    BFun arg body stack -> do
                        xC <- evalExpr x
                        usingStack (Map.insert arg xC stack) (evalExpr body)
                    BFunBuiltin runner -> do
                        xC <- evalExpr x
                        runner xC
                    _ -> throwError $ InternalError "called non-function"
    Tuple es -> do
        cs <- mapM evalExpr es
        CPtr <$> malloc (BTuple cs)
    Fun xs body -> do
        stack <- getStack
        boxed <- evalFun stack xs body
        CPtr <$> malloc boxed
    Let x rhs body -> do
        rhsC <- evalExpr rhs
        withVar x rhsC (evalExpr body)
    LetRec bindings body -> do
        stack' <- evalRecBindings bindings
        usingStack stack' (evalExpr body)
    Match e cases -> do
        eC <- evalExpr e
        evalMatchCases eC cases
    Con c -> cellOfVar c

-- | tries each pattern and picks the first one that works
evalMatchCases :: Cell -> [(Pattern, Expr)] -> Interpreter Cell
evalMatchCases _ [] = throwError PatternMatchFail
evalMatchCases c ((p,rhs):rest) = catchError (tryMatchCase c p rhs) onError
    where
        onError = \case
            PatternMatchFail -> evalMatchCases c rest
            e -> throwError e

-- | if the value fits the pattern, eval the rhs. Otherwise, fail.
tryMatchCase :: Cell -> Pattern -> Expr -> Interpreter Cell
tryMatchCase c p rhs = do
    stackAdds <- patternMatch c p
    withStack stackAdds (evalExpr rhs)

-- | if the value fits the pattern, return the pattern's bindings. Otherwise, fail.
patternMatch :: Cell -> Pattern -> Interpreter Stack
patternMatch c p = case (c,p) of
    (_,PVar x) -> return $ Map.singleton x c
    (CPtr addr, PTuple ps) -> boxedOfAddr addr >>= \case
        BTuple cs -> do
            stacks <- zipWithM patternMatch cs ps
            return $ mconcat stacks
        _ -> throwError PatternMatchFail
    (CPtr addr, PCon con mP) -> boxedOfAddr addr >>= \case
        BCon con' mCell -> do
            unless (con == con') (throwError PatternMatchFail)
            case (mCell, mP) of
                (Nothing,Nothing) -> return mempty
                (Just c', Just p') -> patternMatch c' p'
                _ -> throwError $ InternalError "pcon arity error at runtime?"
        _ -> throwError PatternMatchFail

evalCell :: Cell -> Interpreter Value
evalCell = \case
    CPtr addr -> evalBoxed =<< boxedOfAddr addr

evalBoxed :: Boxed -> Interpreter Value
evalBoxed = \case
    BFun arg body stack -> return $ VFun arg body stack
    BFunBuiltin{} -> return VFunBuiltin
    BTuple cs -> VTuple <$> mapM evalCell cs
    BCon con Nothing -> return $ VCon con Nothing
    BCon con (Just c) -> VCon con . Just <$> evalCell c
    BNull -> throwError $ InternalError "eval BNull"

evalExpr' :: Expr -> Interpreter Value
evalExpr' = evalExpr >=> evalCell

evalVCon :: String -> Maybe a -> Boxed
evalVCon name Nothing = BCon name Nothing
evalVCon name Just{} = BFunBuiltin $ \c -> CPtr <$> malloc (BCon name (Just c))

evalTopDecls :: [TopDecl] -> Interpreter Stack
evalTopDecls [] = ask
evalTopDecls (decl:rest) = let mRest = evalTopDecls rest in case decl of
    LetDecl x rhs -> do
        c <- evalExpr rhs
        withVar x c mRest
    LetRecDecl bindings -> do
        stack' <- evalRecBindings bindings
        usingStack stack' mRest
    TyDecl _ _ cons -> do
        let conNames = fmap fst cons
            boxes = fmap (uncurry evalVCon) cons
        cells <- mapM (fmap CPtr . malloc) boxes
        withVars (zip conNames cells) mRest

evalProg :: Program -> Interpreter (Stack, Maybe Value)
evalProg (Program decls) = do
    stack <- evalTopDecls decls
    vals <- mapM evalCell stack
    return (stack, Map.lookup "main" vals)

executeInterpreter :: Interpreter a -> (Either RuntimeError a, Store)
executeInterpreter =
    runInterpreter
    >>> runExceptT
    >>> (\m -> runRWS m emptyEnv emptyStore)
    >>> (\(a,s,_) -> (a,s))

interpretExpr :: Expr -> (Either RuntimeError Cell, Store)
interpretExpr = executeInterpreter . evalExpr

interpretProgram :: Program -> (Either RuntimeError (Stack, Maybe Value), Store)
interpretProgram = executeInterpreter . evalProg
