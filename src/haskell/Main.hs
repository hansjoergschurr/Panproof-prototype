{-# OPTIONS_GHC -Wall #-}

module Main where

import API
import Control.Monad.Trans.Class (lift)
import Control.Monad ( foldM )
import Text.Printf ( printf )
import Data.Map (Map)
import System.Environment (getArgs)
import qualified Data.Map as Map

{-
This is a quick and dirty implementation of a proof checker.
It uses the proof rules exported from the Agda side.  The API doesn't
enforce that we check the proof correctly.  

The rules to elaborate are given as command line arguments.

A small complication is that the premises of an elaborated step
become assumptions of the proof tree it elaborates to.
To stitch this together, we use a global map of printed sequents.
This is likely overkill in practice.
-}

-- Used to store the index assigned to sequents
type SeqMap = Map Sequent Int

-- The result of checking a step:
-- - the proved sequent
-- - its index
-- - the currently largest printing index
-- - the current sequent mapping.
type CheckRes = (Sequent, Int, Int, SeqMap)

-- Helper to fold over a list of premises.
checkFold :: ([Sequent], Int, [Int], SeqMap) -> Step -> Checker ([Sequent], Int, [Int], SeqMap)
checkFold (seqs, cnt, idxs, am) s = do
    (se, cnt', idx , am') <- checkProof am cnt s
    return (se : seqs, cnt', idx:idxs, am')

checkProof :: SeqMap -> Int -> Step -> Checker CheckRes
checkProof am cnt (Assume _ s)  
    | Map.member s am = return (s, cnt, Map.findWithDefault (-1) s am, am)
    | otherwise = do
        lift $ printf "%d assert %s\n" cnt (show s)
        return (s, cnt + 1, cnt, Map.insert s cnt am)
checkProof am cnt (Step _ (Axiom name check) s args) = do
    (prems, cnt', ns, am') <- foldM checkFold ([], cnt, [], am) s
    case check (reverse prems) args of
        Nothing -> error $ "Checking axiom failed!" ++ show prems
        Just out -> do
            lift $ printf "%d use axiom %7s on %s\t%s\n" cnt' name (show ns) (show out)
            return (out, cnt' + 1, cnt', Map.insert out cnt' am')
checkProof am cnt (Step _ (Rule name check elab) s args) = do
    toElaborate <- lift getArgs
    if name `elem` toElaborate then do
        (prems, cnt', _, am') <- foldM checkFold ([], cnt, [], am) s
        case elab (reverse prems) args of
            Nothing -> error "Elaboration rule step failed!"
            Just elaborated -> checkProof am' cnt' elaborated
    else do
        (prems, cnt', ns, am') <- foldM checkFold ([], cnt, [], am) s
        case check (reverse prems) args of
            Nothing -> error "Checking rule failed!"
            Just out -> do 
                lift $ printf "%d use rule  %7s on %s\t%s\n" cnt' name (show ns) (show out) 
                return (out, cnt' + 1, cnt', Map.insert out cnt' am')

termTest :: Checker ()
termTest = do
    t <- land @ lA @ lB
    lift $ print t

proofTest1 :: Checker ()
proofTest1 = do
    t1 <- land @ lA @ (land @ lA @ lB)
    t2 <- lnot @ (lnot @ lC)
    let prem = [t1, t2]
    a1 <- mkAssume prem t1
    a2 <- mkAssume prem t2
    s1 <- mkStep prem ruleAndE3 [a1]
    s2 <- mkStep prem axNotnotE [a2]
    s3 <- mkStep prem axAndI [s1, s2]
    _ <- checkProof Map.empty 1 s3
    return ()

proofTest2 :: Checker ()
proofTest2 = do
    t1 <- land @ lA @ (land @ lA @ (lnot @ (lnot @ (lor @ lA @ lB))))
    let prem = [t1]
    a1 <- mkAssume prem t1
    s1 <- mkStep prem ruleAndE3 [a1]
    s2 <- mkStep prem axNotnotE [s1]
    s3 <- mkStep prem ruleOrSym [s2]
    _ <- checkProof Map.empty 1 s3
    return ()

main :: IO ()
main = runChecker proofTest2
