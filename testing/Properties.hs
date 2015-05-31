{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}

module Properties where

import Control.Monad

import qualified Debug.Trace as Trace

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

import qualified Compiler.Hoopl.Block as Block
import qualified Compiler.Hoopl.Collections as Collections
import qualified Compiler.Hoopl.Dataflow as Dataflow
import qualified Compiler.Hoopl.Graph as Graph
import qualified Compiler.Hoopl.Fuel as Fuel
import qualified Compiler.Hoopl.Label as Label
import qualified Compiler.Hoopl.Unique as Unique

import qualified Ast
import qualified Ast2ir
import qualified Ir2ast
import qualified ConstProp
import qualified IR
import qualified Live
import qualified Test

-- FIXME: this should go to Test module
-- ===>
testFwdPass
    :: Dataflow.FwdPass
           (Fuel.CheckingFuelMonad Unique.SimpleUniqueMonad)
           IR.Insn
           ConstProp.ConstFact
testFwdPass = Test.constPropPass

testBwdPass
    :: Dataflow.BwdPass
           (Fuel.CheckingFuelMonad Unique.SimpleUniqueMonad)
           IR.Insn
           Live.Live
testBwdPass =
    Dataflow.BwdPass
        { Dataflow.bp_lattice = Live.liveLattice
        , Dataflow.bp_transfer = Live.liveness
        , Dataflow.bp_rewrite = Live.deadAsstElim }

optimizeIr
    :: IR.Proc
    -> IR.M ( IR.Proc
            , Label.FactBase ConstProp.ConstFact
            , IR.Proc
            , Label.FactBase Live.Live
            )
optimizeIr procedure@(IR.Proc _ args entry body) = do
    let fwdInitMap = Collections.mapSingleton entry (ConstProp.initFact args)
        bwdInitMap = Collections.mapEmpty
        entryBlock = Block.JustC [entry]
    (optFwd, fwdResult, _) <-
        Dataflow.analyzeAndRewriteFwd testFwdPass entryBlock body fwdInitMap
    (optFwdBwd, bwdResult, _) <-
        Dataflow.analyzeAndRewriteBwd testBwdPass entryBlock optFwd bwdInitMap
    let optFwdProc = procedure { IR.body = optFwdBwd }
        optFwdBwdProc = procedure { IR.body = optFwdBwd }
    return (optFwdProc, fwdResult, optFwdBwdProc, bwdResult)

runOptimizeIr
    :: IR.Proc
    -> ( IR.Proc
       , Label.FactBase ConstProp.ConstFact
       , IR.Proc
       , Label.FactBase Live.Live
       )
runOptimizeIr = runMonads . optimizeIr

runMonads :: Fuel.CheckingFuelMonad Unique.SimpleUniqueMonad c -> c
runMonads = Unique.runSimpleUniqueMonad . Fuel.runWithFuel (maxBound :: Int)

-- testFwdPass
--   :: Hoopl.FuelMonad m => Hoopl.FwdPass m IR.Insn ConstProp.ConstFact
-- testFwdPass = constPropPass

-- testBwdPass :: Hoopl.FuelMonad m => Hoopl.BwdPass m IR.Insn Live.Live
-- testBwdPass =
--     Hoopl.BwdPass
--         { Hoopl.bp_lattice = Live.liveLattice
--         , Hoopl.bp_transfer = Live.liveness
--         , Hoopl.bp_rewrite = Live.deadAsstElim }


-- <===

-- Is this necessary? Maybe remove this for readability????
optimizeAst
    :: Ast.Proc
    -> ( Ast2ir.IdLabelMap
       , IR.Proc
       , Label.FactBase ConstProp.ConstFact
       , IR.Proc
       , Label.FactBase Live.Live
       )
optimizeAst = Unique.runSimpleUniqueMonad . Fuel.runWithFuel (maxBound :: Int) . doOptimize
  where
    doOptimize ast = do
      (labelMap, ir) <- Ast2ir.astToIR ast
      (optFwd, fwdResult, optBwd, bwdResult) <- optimizeIr ir
      return (labelMap, optFwd, fwdResult, optBwd, bwdResult)


prop_nothingCrashes :: Ast.Proc -> Bool
prop_nothingCrashes ast =
    -- Force evaluation of the optimized AST.
    case optimizeAst ast of
        (!_ast, _, _, _, _) -> True

prop_allLabelsHaveFacts :: Ast.Proc -> Bool
prop_allLabelsHaveFacts ast =
    case optimizeAst ast of
        (labelMap, fwdProc, fwdFact, bwdProc, bwdFacts) ->
            -- let reachable = Ast.reachableLbls (Ir2ast.irToAst labelMap fwdProc)
            let reachable = reachable2_ labelMap fwdProc
                fwd = all (\l -> Collections.mapMember (Maybe.fromJust $ Map.lookup l labelMap) fwdFact) reachable
          in Trace.trace (show $ reachable2_ labelMap fwdProc) fwd

prop_hasReachedFixpoint :: Ast.Proc -> Bool
prop_hasReachedFixpoint ast =
    case optimizeAst ast of
        (labelMap, fwdProc, fwdFact, bwdProc, bwdFacts) ->
            let (fwdProc2, fwdFact2, _, _) = runOptimizeIr fwdProc
            in case IR.showProc fwdProc == IR.showProc fwdProc2 of
              True -> True
              False -> Trace.trace ("\nstrings\nbefore\n" ++ show ast ++ "\nlhs\n" ++ show fwdFact ++ "\nrhs\n" ++ show fwdFact2 ++ "\n" ++ IR.showProc fwdProc ++ "\n" ++ IR.showProc fwdProc2) $ False

-- reachable_ =
--    map Graph.entryLabel . Graph.postorder_dfs . IR.body
reachable2_ :: Map.Map String Label.Label -> IR.Proc -> [String]
reachable2_ labelMap = map f . Collections.setElems . Graph.labelsUsed . IR.body
  where
    f :: Label.Label -> String
    f label = Maybe.fromJust $ Map.lookup label revLabelMap
    revLabelMap = Map.fromList . map (\(a, b) -> (b, a)) $ Map.toList labelMap

prop_hasReachedFixpoint2 :: Ast.Proc -> Bool
prop_hasReachedFixpoint2 ast =
    case optimizeAst ast of
        (labelMap, fwdProc, fwdFact, bwdProc, bwdFacts) ->
            let (fwdProc2, fwdFact2, _, _) = runOptimizeIr fwdProc
            in case fwdFact == fwdFact2 of
              True -> True
              False -> Trace.trace ("\nfacts\nbefore\n" ++ show ast ++ "\nlhs\n" ++ show fwdFact ++ "\nrhs\n" ++ show fwdFact2 ++ "\n" ++ IR.showProc fwdProc ++ "\n" ++ IR.showProc fwdProc2) $ False


-- TODO:
-- Implement equality for the Facts in tests
-- What about graph equality???
-- Optimize once (save the result) and then optimize the second time
-- Check that the second time doesn't change anything (both the graph and facts are "equivalent")
-- Do the same for both forward and backward stuff
