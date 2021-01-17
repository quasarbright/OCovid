{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module OCovid.Eval.Eval where

import Control.Monad.RWS.Strict
import Control.Monad.Except

import OCovid.Syntax.Expr
import OCovid.Syntax.Program

import Data.Map(Map)
import qualified Data.Map as Map

-- types --

data RuntimeError = PatternMatchFail
                  | InternalError String
                  | UnboundVar String
                  | UnboundAddr Addr
                  deriving(Eq, Ord, Show)

-- | heap things. complex structures
data Boxed = BFun String Expr Stack -- a function has the variables it closes over
           | BCon String (Maybe Cell)
           | BTuple [Cell]
           | BNull -- for letrec
           deriving(Eq, Ord, Show)

-- | primitives/pointers. like a word of memory
newtype Cell = CPtr Addr
             -- primitives will go here
             deriving(Eq, Ord, Show)

data Value = VFun String Expr Stack
           | VCon String (Maybe Value)
           | VTuple [Value]
           -- primitives will go here
           deriving(Eq, Ord, Show)

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
withVars vars = local (Map.union (Map.fromList vars))

-- | adds to the stack
withStack :: Stack -> Interpreter a -> Interpreter a
withStack vars = local (Map.union vars)

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
        stack' = Map.fromList stackAdds `Map.union` stack
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
            return $ Map.unions stacks
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
    BTuple cs -> VTuple <$> mapM evalCell cs
    BCon con Nothing -> return $ VCon con Nothing
    BCon con (Just c) -> VCon con . Just <$> evalCell c

evalExpr' :: Expr -> Interpreter Value
evalExpr' = evalExpr >=> evalCell

--
--    Fun [x] body -> VFun x body <$> ask
--    Fun xs body -> evalExpr =<< curryFun xs body
--    Tuple es -> VTuple <$> mapM evalExpr es
--    LetRec [(x,Fun [arg] fbody)] body -> do
--        fbod