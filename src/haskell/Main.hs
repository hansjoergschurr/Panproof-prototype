{-# OPTIONS_GHC -Wall #-}

module Main where

import API
import Control.Monad.Trans.Class (lift)
import Control.Monad
import Text.Printf
import Data.Map (Map)
import qualified Data.Map as Map


toElaborate :: [String]
toElaborate = ["andE3"]

{-
This is a quick and dirty implementation of a proof checker.
It uses the proof rules exported from the Agda side.  The API doesn't
enforce that we check the proof correctly.  

Adjust the `toElaborate` list above to change the rules that
should be elaborated.

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
        lift $ printf "%d assume\t\t%s\n" cnt (show s)
        return (s, cnt + 1, cnt, Map.insert s cnt am)
checkProof am cnt (Step _ (Axiom name check) s _) = do
    (prems, cnt', ns, am') <- foldM checkFold ([], cnt, [], am) s
    case check prems [] of 
        Nothing -> error "Proof checking failed!"
        Just out -> do
            lift $ printf "%d step    %7s %s\t%s\n" cnt' name (show ns) (show out)
            return (out, cnt' + 1, cnt', Map.insert out cnt' am')
checkProof am cnt (Step _ (Rule name check elab) s _)
    | name `elem` toElaborate = do
        (prems, cnt', _, am') <- foldM checkFold ([], cnt, [], am) s
        case elab prems [] of
            Nothing -> error "Proof checking failed!"
            Just elaborated -> checkProof am' cnt' elaborated
    | otherwise = do
        (prems, cnt', ns, am') <- foldM checkFold ([], cnt, [], am) s
        case check prems [] of 
            Nothing -> error "Proof checking failed!"
            Just out -> do 
                lift $ printf "%d step    %7s %s\t%s\n" cnt' name (show ns) (show out) 
                return (out, cnt' + 1, cnt', Map.insert out cnt' am')

termTest :: Checker ()
termTest = do
    t <- land @ lA @ lB
    lift $ print t

proofTest :: Checker ()
proofTest = do
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

main :: IO ()
main = runChecker proofTest
