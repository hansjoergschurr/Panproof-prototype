{-# OPTIONS_GHC -Wall #-}

module Main where

import API
import Control.Monad.Trans.Class (lift)

toElaborate :: [String]
toElaborate = ["andE3"]

checkProof :: Int -> Step -> Checker Sequent
checkProof n (Assume _ s) = do
    let space = replicate n ' '
    lift $ putStrLn (space ++ "assume\t\t" ++ show s)
    return s
checkProof n (Step _ (Axiom name check) s _) = do
    prems <- mapM (checkProof (n + 2)) s
    case check prems [] of 
        Nothing -> error "Proof checking failed!"
        Just out -> do
            let space = replicate n ' '
            lift $ putStrLn (space ++ "step\t" ++ name ++ "\t" ++ show out)
            return out
checkProof n (Step _ (Rule name check elab) s _)
    | name `elem` toElaborate = do
        -- TODO: we print some fake assumptions here, because we don't correctly
        -- "stech the rule back in"
        prems <- mapM (checkProof (n + 2)) s
        case elab prems [] of
            Nothing -> error "Proof checking failed!"
            Just elaborated -> checkProof n elaborated
    | otherwise = do
        prems <- mapM (checkProof (n + 2)) s
        case check prems [] of 
            Nothing -> error "Proof checking failed!"
            Just out -> do 
                let space = replicate n ' '
                lift $ putStrLn (space ++ "step\t" ++ name ++ "\t" ++ show out)
                return out

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
    _ <- checkProof 0 s3
    return ()

main :: IO ()
main = runChecker proofTest
