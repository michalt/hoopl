{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module Ast (Proc(..), Block(..), Insn(..), Control(..), Lbl, showProc, reachableLbls) where

import Control.Monad
import Data.List

import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Test.QuickCheck.Arbitrary as Arb
import qualified Test.QuickCheck.Gen as Gen


import Expr
import PP

-- | A procedure has a name, a sequence of arguments, and a body,
--   which is a sequence of basic blocks. The procedure entry
--   is the first block in the body.
data Proc = Proc { name :: String, args :: [Var], body :: [Block] } deriving Eq

-- | A block consists of a label, a sequence of instructions,
--   and a control-transfer instruction.
data Block = Block { first :: Lbl, mids :: [Insn], last :: Control } deriving Eq

-- | An instruction is an assignment to a variable or a store to memory.
data Insn = Assign Var  Expr
          | Store  Expr Expr deriving (Eq)

-- | Control transfers are branches (unconditional and conditional),
--   call, and return.
--   The Call instruction takes several parameters: variables to get
--   values returned from the call, the name of the function,
--   arguments to the function, and the label for the successor
--   of the function call.
data Control = Branch Lbl
             | Cond   Expr   Lbl    Lbl
             | Call   [Var]  String [Expr] Lbl
             | Return [Expr] deriving (Eq)

-- | Labels are represented as strings in an AST.
type Lbl = String

instance Show Proc where
  show = showProc

showProc :: Proc -> String
showProc (Proc { name = n, args = as, body = blks})
  = n ++ tuple as ++ graph
  where
    graph  = foldl (\p b -> p ++ "\n" ++ show b) (" {") blks ++ "\n}\n"

instance Show Block where
  show (Block f m l) = (foldl (\p e -> p ++ "\n" ++ show e) (f++":") m) ++ "\n" ++ show l

instance Show Insn where
  show (Assign v e)       = ind $ v ++ " = " ++ show e
  show (Store addr e)     = ind $ "m[" ++ show addr ++ "] = " ++ show e

instance Show Control where
  show (Branch lbl)       = ind $ "goto " ++ lbl
  show (Cond e t f)       =
    ind $ "if " ++ show e ++ " then goto " ++ t ++ " else goto " ++ f
  show (Call ress f cargs successor) =
    ind $ tuple ress ++ " = " ++ f ++ tuple (map show cargs) ++ " goto " ++ successor
  show (Return      rargs) = ind $ "ret " ++ tuple (map show rargs)

ind :: String -> String
ind x = "  " ++ x

{-
instance Show Value where
  show (B b) = show b
  show (I i) = show i
-}

-- | The state when generating a new AST.
data ProcState = ProcState
    { psName :: !String              -- ^ The procedure name.
    , psLbls :: ![Lbl]               -- ^ The list of all available labels.
    , psVars :: ![Var]               -- ^ The list of all available variables.
    , psSize :: {-# UNPACK #-} !Int  -- ^ The current size.
    }

instance Arb.Arbitrary Proc where
  arbitrary = Gen.sized arbProc
  shrink = shrinkProc

--
-- Helper data and functions to decide what kind of AST node to create (e.g., if
-- we want to generate an Expr, which one?).
--

data WhatInsn = DoAssign | DoStore

data WhatExpr = DoLit | DoVar | DoLoad | DoBinop

data WhatCtrl = DoBranch | DoCond | DoReturn | DoCall

whatInsn :: Gen.Gen WhatInsn
whatInsn = Gen.elements [ DoAssign, DoStore ]

whatExpr :: Int -> Gen.Gen WhatExpr
whatExpr 0 = Gen.elements [ DoLit, DoVar ]
whatExpr _ = Gen.elements [ DoLit, DoVar, DoLoad, DoBinop ]

whatCtrl :: Gen.Gen WhatCtrl
whatCtrl =
   -- This will favor inter-block jumps so that we get more complicated graphs.
   Gen.frequency [ (3, return DoCond)
                 , (2, return DoBranch)
                 , (1, return DoReturn)
                 , (1, return DoCall)
                 ]

--
-- Implementation of Arbitrary
--

-- | Given a size parameter, generate and return a procedure.
--
-- Note that the size
-- parameter must be greater than 1.
arbProc :: Int -> Gen.Gen Proc
arbProc 0    = arbProc 1  -- Ast2ir expects non empty procuderes
arbProc size = do
  let name = "procName"
  let vars = map (\v -> "var" ++ show v) [0.. size]
      lbls = createLabels size
  body <- generateBody (ProcState name lbls vars size)
  return $! Proc name vars body

-- | Generate the body of a procedure.
--
-- The only interesting aspect of this is that we always generate at least two
-- blocks: one for entry and one for exit.
generateBody :: ProcState -> Gen.Gen [Block]
generateBody (ProcState _ [] _ _) =
  error "generateBody needs at least one label"
generateBody state@(ProcState _ labels _ _) = do
  let entryLbl = head labels
      otherLbls = tail labels
  entryBlock <- generateEntryBlock state entryLbl
  innerBlocks <- mapM (generateBlock state) otherLbls
  return $! entryBlock : innerBlocks

generateBlock :: ProcState -> Lbl -> Gen.Gen Block
generateBlock state lbl = do
  insns <- generateInsns state
  ctrl <- generateCtrl state
  return $! Block lbl insns ctrl

generateEntryBlock :: ProcState -> Lbl -> Gen.Gen Block
generateEntryBlock state myLbl = do
  insns <- generateInsns state
  expr <- generateExpr state
  lbl1 <- generateLbl state
  lbl2 <- generateLbl state
  return $! Block myLbl insns (Cond expr lbl1 lbl2)

generateInsns :: ProcState -> Gen.Gen [Insn]
generateInsns state = do
  num <- Gen.choose (0, psSize state `div` 4)
  sequence . take num $ repeat (generateInsn state)

generateInsn :: ProcState -> Gen.Gen Insn
generateInsn state = do
  kind <- whatInsn
  case kind of
    DoAssign -> do
      var <- Gen.elements $ psVars state
      expr <- generateExpr state
      return $! Assign var expr
    DoStore  -> do
      addr <- generateExpr state
      value <- generateExpr state
      return $! Store addr value

generateExpr :: ProcState -> Gen.Gen Expr
generateExpr state@(ProcState _ _ vars size) = do
  kind <- whatExpr size
  case kind of
    DoLit -> Arb.arbitrary >>= \l -> return $! Lit l
    DoVar -> do
      var <- Gen.elements vars
      return $! Var var
    DoBinop -> do
      lhs <- generateExpr $ state { psSize = size `div` 2 }
      rhs <- generateExpr $ state { psSize = size `div` 2 }
      op <- Arb.arbitrary
      return $! Binop op lhs rhs
    DoLoad -> do
      addr <- generateExpr $ state { psSize = size `div` 2 }
      return $! Load addr

generateCtrl :: ProcState -> Gen.Gen Control
generateCtrl state = do
  kind <- whatCtrl
  case kind of
    DoBranch -> liftM Branch $ generateLbl state
    DoReturn -> do
      expr <- generateExpr state
      return $! Return [expr]
    DoCond -> do
      true <- generateLbl state
      false <- generateLbl state
      expr <- generateExpr state
      return $! Cond expr true false
    DoCall -> do
      args <- sequence . take (psSize state) $ repeat (generateExpr state)
      retLbl <- generateLbl state
      return $! Call (psVars state) (psName state) args retLbl

--
-- Helper functions
--

createLabels :: Int -> [Lbl]
createLabels size = map (\l -> "L" ++ show l) [0.. size]

generateLbl :: ProcState -> Gen.Gen Lbl
generateLbl = Gen.elements . psLbls

-- | Computes the labels reachable from the entry point of the procedure (i.e.,
-- its first block).
reachableLbls :: Proc -> [Lbl]
reachableLbls (Proc _ _ []) = []
reachableLbls (Proc _ _ blocks) = Set.toList $ go [entry] Set.empty
  where
    entry = first . head $ blocks
    blockMap =
      let extractLbls (Return _) = []
          extractLbls (Call {}) = []
          extractLbls (Branch l) = [l]
          extractLbls (Cond _ t f) = [t, f]
      in Map.fromList $ map (\(Block l _ c) -> (l, extractLbls c)) blocks
    go [] reachable = reachable
    go (lbl : rest) reachable1
      | Set.member lbl reachable1 = go rest reachable1
      | otherwise =
      let reachable2 = Set.insert lbl reachable1
      in case Map.lookup lbl blockMap of
        Nothing -> error "The map should contain all the labels"
        Just [] -> go rest reachable2
        Just lbls -> go (lbls ++ rest) reachable2

--
-- Shrinking code
--

-- | Shrink the given procedure by trying to remove blocks, variables and
-- statements.
--
-- We could probably do much more sophisticated removals, but these were quite
-- sufficient so far (and there is always a computational cost if we generate
-- many more alternatives).
shrinkProc :: Proc -> [Proc]
shrinkProc (Proc _ _ [_lastBlock]) = []  -- Ast2ir expects at least one block
shrinkProc (Proc name vars blocks1) =
    -- First let's try to remove whole blocks (while remapping all the other
    -- ones to refer to some other block than the removed).
    [ Proc name vars (blocksRemoveLbl toRm (exitInstead toRm) blocks1)
    | toRm <- allLabels ]
    ++
    -- Then try to remove variables (again trying to replace the removed one
    -- with some other one).
    [ Proc name newVars (blocksRemoveVar toRm (head newVars) blocks1)
    | toRm <- vars, newVars <- varInstead toRm  ]
    ++
    -- Finally, try to remove particular statements.
    [ Proc name vars (blocksRemoveNthStmt n blocks1)
    | n <- [0.. maxStmts - 1] ]
  where
    allLabels = map first blocks1
    revAllLabels = reverse allLabels
    -- We can't simply take the last label of allLabels to be the exit label,
    -- since this might be the label we're trying to remove. So we take the last
    -- available label as the replacement for the removed one.
    exitInstead lbl =
      let revRemaining = delete lbl revAllLabels
      in if null revRemaining then lbl else head revRemaining
    varInstead toRm =
      let remaining = delete toRm vars
      in if null remaining then [] else [remaining]
    maxStmts = maximum $ map (length . mids) blocks1

blocksRemoveVar :: Var -> Var -> [Block] -> [Block]
blocksRemoveVar toRm newVar = map f
  where
    f (Block lbl insns ctrl) = Block lbl (map rmInsn insns) (rmCtrl ctrl)
    rmInsn (Assign var expr) | var == toRm = Assign newVar (rmExpr expr)
                             | otherwise   = Assign var (rmExpr expr)
    rmInsn (Store lhs rhs) = Store (rmExpr lhs) (rmExpr rhs)
    rmExpr v@(Var var) | var == toRm = Var newVar
                       | otherwise   = v
    rmExpr (Load expr) = Load (rmExpr expr)
    rmExpr (Binop op lhs rhs) = Binop op (rmExpr lhs) (rmExpr rhs)
    rmExpr l@(Lit {}) = l
    rmCtrl call@(Call vars name exprs lbl) =
      case elemIndex toRm vars of
        Nothing -> call
        Just n  -> Call (deleteNth n vars) name (deleteNth n exprs) lbl
    rmCtrl ctrl = ctrl

blocksRemoveNthStmt :: Int -> [Block] -> [Block]
blocksRemoveNthStmt n = map f
  where
    f (Block lbl insns ctrl) = Block lbl (deleteNth n insns) ctrl

blocksRemoveLbl :: Lbl -> Lbl -> [Block] -> [Block]
blocksRemoveLbl oldLbl newLbl = concatMap f
  where
    f (Block lbl insns ctrl)
      | lbl == oldLbl = []
      | otherwise     =
        [ Block lbl insns (controlReplaceLbl oldLbl newLbl ctrl) ]

controlReplaceLbl :: Lbl -> Lbl -> Control -> Control
controlReplaceLbl oldLbl newLbl ctrl =
  case ctrl of
    ret@(Return {}) -> ret
    call@(Call {}) -> call
    (Branch lbl)   -> Branch (subst lbl)
    (Cond b true false) -> Cond b (subst true) (subst false)
  where
    subst lbl
      | lbl == oldLbl = newLbl
      | otherwise     = lbl

deleteNth :: Int -> [a] -> [a]
deleteNth n list | length list > n = take n list ++ drop (n + 1) list
                 | otherwise       = list
