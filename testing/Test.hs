{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, GADTs, EmptyDataDecls, PatternGuards, TypeFamilies, NamedFieldPuns #-}
module Test (parseTest, evalTest, optTest) where

import Control.Monad.Except
import System.Exit

import Compiler.Hoopl

import qualified Ast as A
import qualified Ir2ast as Ia
import Ast2ir
import ConstProp
import Eval (evalProg)
import IR
import Live
import Parse (parseCode)
import Simplify

parse :: String -> String -> M [(IdLabelMap, Proc)]
parse file text =
  case parseCode file text of
    Left  err -> error $ show err
    Right ps  -> mapM astToIR ps

parseTest :: String -> IO ()
parseTest file = do
  text <- readFile file
  let p = parse file text
  mapM_ (putStrLn . showProc . snd) (runMonadsWith 0 p)

evalTest' :: String -> String -> String
evalTest' file text = do
  let procs = parse file text
      (_, vs) = (testProg . snd . unzip) (runMonadsWith 0 procs)
  "returning: " ++ show vs
  where
    testProg procs@(Proc {name, args} : _) = evalProg procs vsupply name (toV args)
    testProg _ = error "No procedures in test program"
    toV args = [I n | (n, _) <- zip [3..] args]
    vsupply = [I x | x <- [5..]]

evalTest :: String -> IO ()
evalTest file = readFile file >>= putStrLn . evalTest' file

optTest' :: [Proc] -> M [Proc]
optTest' = mapM optProc
  where
    optProc proc@(Proc {entry, body, args}) = do
      let justEntry = JustC [entry]
          fwdInit = mapSingleton entry (initFact args)
          bwdInit = mapEmpty
      (body',  _, _) <-
        analyzeAndRewriteFwd testFwdPass justEntry body fwdInit
      (body'', _, _) <-
        analyzeAndRewriteBwd testBwdPass justEntry body' bwdInit
      return $ proc { body = body'' }

constPropPass :: FuelMonad m => FwdPass m Insn ConstFact
-- @ start cprop.tex

----------------------------------------
-- Defining the forward dataflow pass
constPropPass = FwdPass
  { fp_lattice  = constLattice
  , fp_transfer = varHasLit
  , fp_rewrite  = constProp `thenFwdRw` simplify }
-- @ end cprop.tex

testFwdPass :: FuelMonad m => FwdPass m Insn ConstFact
testFwdPass = constPropPass

testBwdPass :: FuelMonad m => BwdPass m Insn Live
testBwdPass = BwdPass
  { bp_lattice = liveLattice
  , bp_transfer = liveness
  , bp_rewrite = deadAsstElim }


toAst :: [(IdLabelMap, Proc)] -> [A.Proc]
toAst l = fmap (uncurry Ia.irToAst) l

compareAst :: [A.Proc] -> [A.Proc] -> IO ()
compareAst [] [] = return ()
compareAst (r:results) (e:expected) =
  if r == e
  then compareAst results expected
  else do
    putStrLn "expecting"
    putStrLn $ A.showProc e
    putStrLn "resulting"
    putStrLn $ A.showProc r
    putStrLn "the result does not match the expected, abort the test!!!!"
    exitFailure

compareAst results expected = do
  putStrLn "expecting"
  mapM_ (putStrLn . A.showProc) expected
  putStrLn "resulting"
  mapM_ (putStrLn . A.showProc) results
  putStrLn "the result does not match the expected, abort the test!!!!"
  exitFailure

optTest :: String -> String -> IO ()
optTest file expectedFile =
  do text    <- readFile file
     expectedText <- readFile expectedFile
     let lps = parse file text
         exps = parse expectedFile expectedText
     case (optTest' . snd . unzip) =<< lps of
       p  -> do
         let opted = runMonads p
             lbmaps = runMonads (liftM (fst . unzip) lps)
             expected = runMonads exps
         compareAst (toAst (zip lbmaps opted)) (toAst expected)

runMonads :: CheckingFuelMonad SimpleUniqueMonad c -> c
runMonads = runSimpleUniqueMonad . runWithFuel (maxBound :: Int)

runMonadsWith :: Int -> CheckingFuelMonad SimpleUniqueMonad c -> c
runMonadsWith fuel = runSimpleUniqueMonad . runWithFuel fuel


{-- Properties to test:

  1. Is the fixpoint complete (maps all blocks to facts)?
  2. Is the computed fixpoint actually a fixpoint?
  3. Random test generation.

--}
