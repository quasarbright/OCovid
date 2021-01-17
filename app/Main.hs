{-# LANGUAGE LambdaCase #-}

module Main where

import OCovid.Parsing.Parse
import OCovid.Static.WellFormedness
import OCovid.Static.Typing
import OCovid.Eval.Eval
import OCovid.Run

import System.Environment
import Control.Monad (void)

swallowS :: Either String r -> r
swallowS = \case
    Left s -> errorWithoutStackTrace s
    Right r -> r
    
swallow :: Show err => Either err r -> r
swallow = \case
    Left err -> errorWithoutStackTrace (show err)
    Right r -> r

main = do
    getArgs >>= \case
        [] -> errorWithoutStackTrace "no file"
        path:_ -> do
            contents <- readFile path
            case swallow (runProg path contents) of
                Nothing -> putStrLn "program ran successfully, but no main value was found"
                Just v -> print v