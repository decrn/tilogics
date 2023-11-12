module Main where

import Control.Exception
import Control.Monad
import Data.Semigroup ((<>))
import Options.Applicative
import System.Exit

import Infer (Exp, Result(..), ground_expr, infer)
import Instances ()
import Parser (parse)

optionsParser :: Parser String
optionsParser =
  argument str
  (metavar "FILENAME" <>
   help "Path to the file to type check")

parserInfo :: ParserInfo String
parserInfo =
  info
  (optionsParser <**> helper)
  (fullDesc
    <> progDesc "Typecheck FILENAME"
    <> header "em - a typechecker for lambdabool" )

doRead :: String -> IO String
doRead path = handle h $ readFile path
  where
    h :: IOException -> IO String
    h _ = putStrLn "Error: Unable to read the file." >>
          exitWith (ExitFailure 1)

doParse :: String -> IO Exp
doParse content =
  case parse content of
    Left e -> do
      putStrLn "Parsing failed:"
      print e
      exitWith (ExitFailure 1)
    Right e -> do
      putStr "Desugared exp: "
      print e
      return e

doInfer :: Exp -> IO ()
doInfer e =
  case infer e of
    Just r@(MkResult w ot _oe) -> do
      putStr ("Unconstrained: ")
      print w
      putStr ("Inferred type: ")
      print ot
      putStr ("Reconstructed: ")
      print (ground_expr r)

    Nothing -> putStrLn "Inference failed"

main :: IO ()
main =
  execParser parserInfo >>=
  (doRead >=> doParse >=> doInfer)
