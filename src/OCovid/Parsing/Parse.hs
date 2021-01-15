module OCovid.Parsing.Parse where

import Text.Megaparsec
import Text.Megaparsec.Char

import OCovid.Parsing.ParseUtils
import OCovid.Syntax.Expr
import OCovid.Static.Types
import OCovid.Syntax.Program
import Control.Monad (void)
import Data.Functor (($>))

type ExprParser = Parser Expr -> Parser Expr

-- exprs --

pVar :: Parser Expr
pVar = Var <$> identifier

pApp :: ExprParser
pApp child = do
    fargs <- some child
    return (foldl1 App fargs)

-- also normal paren
pTuple :: Parser Expr
pTuple = do
    symbol "("
    exprs <- pExpr `sepBy` symbol ","
    symbol ")"
    case exprs of
        [e] -> return e
        _ -> return (Tuple exprs)

pFun :: Parser Expr
pFun = do
    pKeyword "fun"
    args <- some identifier
    symbol "->"
    body <- pExpr
    return (Fun args body)

pLet :: Parser Expr
pLet = do
    pKeyword "let"
    name <- identifier
    symbol "="
    rhs <- pExpr
    pKeyword "in"
    body <- pExpr
    return (Let name rhs body)

pCase :: Parser (Pattern, Expr)
pCase = (,) <$> (pPattern <* symbol "->") <*> pExpr <?> "match case"

pMatch :: Parser Expr
pMatch = do
    pKeyword "match"
    target <- pExpr
    pKeyword "with"
    void (optional (symbol "|"))
    cases <- pCase `sepBy1` symbol "|"
    return (Match target cases)

pAtom :: Parser Expr
pAtom = choice
    [ pTuple <?> "tuple/parenthesized expression"
    , pVar <?> "variable"
    ]

pExpr :: Parser Expr
pExpr = choice
    [ pLet <?> "let binding"
    , pMatch <?> "match expression"
    , pFun <?> "function expression"
    , pApp pAtom <?> "function application"
    ]

-- patterns --

-- also normal paren
pPTuple :: Parser Pattern
pPTuple = do
    symbol "("
    patterns <- pPattern `sepBy` symbol ","
    symbol ")"
    case patterns of
        [p] -> return p
        _ -> return (PTuple patterns)

pPattern :: Parser Pattern
pPattern =  PVar <$> identifier
        <|> pPTuple

-- types --

pTArr :: Parser Type
pTArr = do
    ts <- pTTuple `sepBy1` symbol "->"
    case ts of
        [t] -> return t
        _ -> return $ foldr1 TArr ts

pTTuple :: Parser Type
pTTuple = do
    ts <- pTCon `sepBy1` symbol "*"
    case ts of
        [t] -> return t
        _ -> return $ TTuple ts

pTCon :: Parser Type
pTCon =
    let pArgs = try (fmap (:[]) pTAtom) <|> parens (pType `sepBy1` symbol ",")
        p = do
            args <- pArgs
            name <- identifier
            return $ TCon name args
    in try p <|> pTAtom

pTAtom :: Parser Type
pTAtom = choice [parens pType, pTVar, pTUnit]

pTVar :: Parser Type
pTVar = string "'" *> fmap TVar identifier

pTUnit :: Parser Type
pTUnit = pKeyword "unit" $> TTuple []

pType :: Parser Type
pType = pTArr

-- programs --

pProgram :: Parser Program
pProgram = Program <$> many bind
    where
        bind = do
            pKeyword "let"
            name <- identifier
            symbol "="
            rhs <- pExpr
            return (name, rhs)

fixLeft :: (Stream s, ShowErrorComponent e) => Either (ParseErrorBundle s e) b -> Either String b
fixLeft m = case m of
    Left e -> Left $ errorBundlePretty e
    Right a -> Right a

makeParseFn :: Parser b -> String -> String -> Either String b
makeParseFn p name src = fixLeft $ runParser (scn *> p <* eof) name src

parseProgram :: String -> String -> Either String Program
parseProgram = makeParseFn pProgram

parseExpr :: String -> String -> Either String Expr
parseExpr = makeParseFn pExpr