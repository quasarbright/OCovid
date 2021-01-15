module OCovid.Parsing.ParseUtils where

import Control.Applicative hiding (some, many)
import Control.Monad (void)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Debug as DBG
import Data.Char (isUpper, isLower)

type Parser = Parsec Void String

dbg :: Show a => String -> Parser a -> Parser a
dbg desc p = (if False then DBG.dbg else (\ _ b -> b)) desc p <?> desc

lineComment :: Parser ()
lineComment = empty

blockComment :: Parser ()
blockComment = L.skipBlockCommentNested "(*" "*)"

-- | whitespace consumer that consumes newlines
scn :: Parser ()
scn = L.space space1 lineComment blockComment

---- | whitespace consumer that doesn't consume newlines
--sc :: Parser ()
--sc = L.space (void $ some (char ' ' <|> char '\t')) lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme scn

symbol :: String -> Parser ()
symbol = void . L.symbol scn

pKeyword :: String -> Parser ()
pKeyword = pKeywordWith scn

pKeywordWith :: Parser () -> String -> Parser ()
pKeywordWith sc' word = void . L.lexeme sc' $ (string word <* notFollowedBy identLetter)

pReservedOp :: String -> Parser ()
pReservedOp = pReservedOpWith scn

pReservedOpWith :: Parser () -> String -> Parser ()
pReservedOpWith sc' name = void . L.lexeme sc' $ (string name <* notFollowedBy opLetter)

reservedWords :: [String]
reservedWords = words "let in rec match with fun if then else unit"

--reservedOps :: [String]
--reservedOps = words "+ - * & / ! || && | \" ' : ; % ^"

identStart :: Parser Char
identStart = satisfy isLower <|> char '_'

upperIdentStart :: Parser Char
upperIdentStart = satisfy isUpper

identLetter :: Parser Char
identLetter = identStart <|> numberChar <|> char '\''

upperIdentLetter :: Parser Char
upperIdentLetter = upperIdentStart <|> numberChar <|> oneOf "'_"

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
 where
   p       = (:) <$> identStart <*> many identLetter
   check x =
     if x `elem` reservedWords
     then fail $ "keyword " ++ show x ++ " cannot be an identifier"
     else return x

upperIdentifier :: Parser String
upperIdentifier = (lexeme . try) (p >>= check)
    where
    p = (:) <$> upperIdentStart <*> many upperIdentLetter
    check x =
        if x `elem` reservedWords
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

opLetter :: Parser Char
opLetter = oneOf "\\|/-+=!@#$%^&*~.?<>"

operator :: Parser String
operator = operatorWith scn

operatorWith :: Parser () -> Parser String
operatorWith sc' = (L.lexeme sc' . try) (p >>= check)
   where
       p = some opLetter
       check x =
           if False --x `elem` reservedOps
           then fail $ "reserved operator " ++ show x ++ " cannot be an identifier"
           else return x

type SS = (SourcePos, SourcePos)

-- | run the given parser and record the source span of the parse
wrapSS :: Parser a -> Parser (a, SS)
wrapSS p = do
    startPos <- getSourcePos
    result <- p
    endPos <- getSourcePos
    return (result, (startPos, endPos))

wrapSSWith :: ((a, SS) -> b) -> Parser a -> Parser b
wrapSSWith f p = f <$> wrapSS p

wrapSSM :: Parser (SS -> a) -> Parser a
wrapSSM p = do
    (f,ss) <- wrapSS p
    return $ f ss
    
combineSS :: (a1, b1) -> (a2, b2) -> (a1, b2)
combineSS a b = (fst a, snd b)

-- | optional with backtracking
vot :: Parser () -> Parser ()
vot = void . try . optional

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

-- | copied from the parsec package:
-- https://hackage.haskell.org/package/parsec-3.1.14.0/docs/src/Text.Parsec.Combinator.html#chainl1
chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op        = do{ x <- p; rest x }
                    where
                      rest x    = do{ f <- op
                                    ; y <- p
                                    ; rest (f x y)
                                    }
                                <|> return x