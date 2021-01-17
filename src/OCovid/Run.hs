{-# LANGUAGE LambdaCase #-}

module OCovid.Run(runProg) where

import OCovid.Parsing.Parse
import OCovid.Static.WellFormedness
import OCovid.Static.Typing
import OCovid.Eval.Eval
import Control.Monad (void)

data Error = ParseError String
           | WFError [WFError]
           | TypeError TypeError
           | RuntimeError RuntimeError
           deriving(Eq, Ord, Show)

left :: (t -> a) -> Either t b -> Either a b
left f = \case
    Left l -> Left (f l)
    Right r -> Right r

runProg :: String -> String -> Either Error (Maybe Value)
runProg path src = do
    prog <- left ParseError (parseProgram path src)
    void $ left WFError (checkProgramWellFormedness prog)
    void $ left TypeError (typeCheckProgram prog)
    let (mmCell,_) = interpretProgram prog
    snd <$> left RuntimeError mmCell