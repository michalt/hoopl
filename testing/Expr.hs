{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module Expr (Expr(..), BinOp(..), Lit(..), Var) where

import qualified Test.QuickCheck.Arbitrary as Arb
import qualified Test.QuickCheck.Gen as Gen

import PP

data Expr = Lit   Lit
          | Var   Var
          | Load  Expr
          | Binop BinOp Expr Expr deriving (Eq)

data BinOp = Add | Sub | Mul | Div | Eq | Ne | Lt | Gt | Lte | Gte deriving Eq

data Lit = Bool Bool | Int Integer deriving Eq
type Var = String

--------------------------------------------------------------------------------
--- Prettyprinting
--------------------------------------------------------------------------------

instance Show Expr where
  show (Lit   i) = show i
  show (Var   v) = v
  show (Load  e) = "m[" ++ show e ++ "]"
  show (Binop b e1 e2) = sub e1 ++ " " ++ show b ++ " " ++ sub e2
    where sub e@(Binop _ _ _) = tuple [show e]
          sub e = show e

instance Show Lit where
  show (Int  i) = show i
  show (Bool b) = show b

instance Show BinOp where
  show Add  = "+"
  show Sub  = "-"
  show Mul  = "*"
  show Div  = "/"
  show Eq   = "="
  show Ne   = "/="
  show Gt   = ">"
  show Lt   = "<"
  show Gte  = ">="
  show Lte  = "<="

instance Arb.Arbitrary Lit where
  arbitrary = Gen.oneof [genLitBool, genLitInteger]

genLitBool :: Gen.Gen Lit
genLitBool = do
  bool <- Arb.arbitrary
  return $! Bool bool

genLitInteger :: Gen.Gen Lit
genLitInteger = do
  int <- Arb.arbitrary
  return $! Int int

instance Arb.Arbitrary BinOp where
  arbitrary = Gen.elements [ Add, Sub, Mul, Div, Eq, Ne, Lt, Lte, Gt, Gte ]
