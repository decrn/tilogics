module Main where

import Control.Exception
import Control.Monad
import Data.Semigroup ((<>))
import Options.Applicative
import System.Exit

import Infer (Exp, Result(..), ground_expr, infer_free, infer_prenex, infer_solved)
import Instances ()
import Parser (parse)

pFile :: Parser String
pFile =
  argument str
  (metavar "FILENAME" <>
   help "Path to the file to type check")

pAlgo :: Parser (Exp -> Maybe Result)
pAlgo =
  flag infer_free infer_free (long "free" <> help "Use the Free monad")
  <|> flag' infer_prenex (long "prenex" <> help "Use the Prenex monad")
  <|> flag' infer_solved (long "solved" <> help "Use the Prenex monad")

pOpts :: Parser (Exp -> Maybe Result, String)
pOpts = (,) <$> pAlgo <*> pFile

opts :: ParserInfo (Exp -> Maybe Result, String)
opts =
  info
  (pOpts <**> helper)
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

doInfer :: (Exp -> Maybe Result) -> Exp -> IO ()
doInfer infer e =
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
main = do
  (infer,file) <- execParser opts
  doRead file >>= (doParse >=> doInfer infer)
