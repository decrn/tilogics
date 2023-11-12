{-# OPTIONS_GHC -Wno-orphans #-}

module Instances where

import Data.List
import Infer

toList :: World -> List String -> List String
toList Nil        = id
toList (Snoc w a) = toList w . (a:)

instance Show World where
  show w = intercalate " " (Prelude.map ('?':) (toList w []))

instance Show Exp where
  showsPrec p e =
    case e of
      Var x         -> showString x
      Infer.True    -> showString "true"
      Infer.False   -> showString "false"
      Ifte e1 e2 e3 -> showParen (p > 0) $
                         showString "if " .
                         showsPrec 0 e1 .
                         showString " then ".
                         showsPrec 0 e2 .
                         showString " else ".
                         showsPrec 0 e3
      Absu x e1     -> showParen (p > 0) $
                         showString "\\" .
                         showString x .
                         showString ". " .
                         showsPrec 0 e1
      Abst x t e1   -> showParen (p > 0) $
                         showString "\\" .
                         showString x .
                         showString ":" .
                         showsPrec 0 t .
                         showString ". " .
                         showsPrec 0 e1
      App e1 e2     -> showParen (p > 1) $
                         showsPrec 1 e1 .
                         showString " " .
                         showsPrec 2 e2

instance Show Ty where
  showsPrec p t =
    case t of
      Bool0         -> showString "bool"
      Func0 t1 t2   -> showParen (p > 0) $
                         showsPrec 1 t1 .
                         showString " -> " .
                         showsPrec 0 t2

instance Show OTy where
  showsPrec p t =
    case t of
      Evar alpha _ -> showString ('?':alpha)
      Bool         -> showString "bool"
      Func t1 t2   -> showParen (p > 0) $
                        showsPrec 1 t1 .
                        showString " -> " .
                        showsPrec 0 t2
