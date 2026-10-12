module Main where

import Control.Monad.Foil (emptyNameMap)
import FreeFoilTypecheck.SystemF.Eval
import FreeFoilTypecheck.SystemF.Parser.Par
import FreeFoilTypecheck.SystemF.Syntax (Term (..), toTermClosed)
import FreeFoilTypecheck.SystemF.Typecheck
import FreeFoilTypecheck.SystemF.TypecheckGen
import FreeFoilTypecheck.SystemF.TypingSig ()

-- main :: IO ()
-- main = getArgs >>= \case
--   ["-gen"] -> do
--     putStrLn "Welcome to REPL! (gen)\n"
--     interact (unlines . map genRepl . lines)
--   _ -> do
--     putStrLn "Welcome to REPL!\n"
--     interact (unlines . map repl . lines)

main :: IO ()
main = do
  let example = "let id = (ΛX. λx:X. x) in id : forall Y. Y -> Y"
  Right (Term a) <- pure $ toTermClosed <$> pTerm (myLexer example)
  Right b <- pure $ bidirectionalInfer @Term emptyNameMap a

  print b
  pure ()

repl :: String -> String
repl input =
  case toTermClosed <$> pTerm tokens of
    Left err -> "Parsing error: " ++ err
    Right e -> case inferType emptyNameMap e of
      Left err -> "Typechecking error: " ++ err
      Right _type -> case newEval emptyNameMap e of
        Left err -> "Evaluation error: " ++ err
        Right outExp -> show outExp
  where
    tokens = myLexer input

genRepl :: String -> String
genRepl input =
  case toTermClosed <$> pTerm tokens of
    Left err -> "Parsing error: " ++ err
    Right et@(Term e) -> case bidirectionalInfer @Term emptyNameMap e of
      Left err -> "Typechecking error: " ++ err
      Right _type -> case newEval emptyNameMap et of
        Left err -> "Evaluation error: " ++ err
        Right outExp -> show outExp
  where
    tokens = myLexer input
