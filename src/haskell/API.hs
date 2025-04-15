{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module API (Term,
            Checker,
            runChecker,
            (@),
            pattern (:·:),
            ltrue,
            lfalse,
            land,
            lor,
            lnot,
            lA,
            lB,
            lC,
            Step,
            pattern Assume,
            pattern Step,
            Sequent,
            ProofRule (..),
            mkAssume,
            mkStep,
            axTrue,
            axAssume,
            axAndI,
            axAndE1,
            axAndE2,
            axNotnotI,
            axNotnotE,
            axOrI1,
            axOrI2,
            axOrE,
            axOrFalseE,
            axNotE,
            axNegI,
            axPBC,
            ruleAndE3,
            ruleOrSym
           )  where

import Control.Monad.Reader
import qualified Core.Terms as T
import qualified Core.Proofs as P
import Core.Proofs (ProofRule (..))
import Core.Rules

type Term = (T.:⊢)

pattern (:·:) :: Term -> Term -> Term
pattern (:·:) t1 t2 = t1 T.:·: t2

-- RedearT with signature and premisses
type Checker = ReaderT T.Signature IO

runChecker :: Checker a -> IO a
runChecker c = runReaderT c T.sig

mkCnst :: Int -> Checker Term
mkCnst i = do
    ctx <- ask
    case T.mkCnst ctx i of
        Nothing -> error "Unkown Constant"
        Just (_, v) -> return v

ltrue, lfalse, land, lor, lnot, lA, lB, lC :: Checker Term
ltrue = mkCnst 0
lfalse = mkCnst 1
land = mkCnst 2
lor = mkCnst 3
lnot = mkCnst 4
lA = mkCnst 5
lB = mkCnst 6
lC = mkCnst 7

pattern Ltrue, Lfalse, Land, Lor, Lnot, LA , LB ,LC :: Term

pattern Ltrue  = T.V T.InZ
pattern Lfalse = T.V (T.InS T.InZ)
pattern Land   = T.V (T.InS (T.InS T.InZ))
pattern Lor    = T.V (T.InS (T.InS (T.InS T.InZ)))
pattern Lnot   = T.V (T.InS (T.InS (T.InS (T.InS T.InZ))))
pattern LA     = T.V (T.InS (T.InS (T.InS (T.InS (T.InS T.InZ)))))
pattern LB     = T.V (T.InS (T.InS (T.InS (T.InS (T.InS (T.InS T.InZ))))))
pattern LC     = T.V (T.InS (T.InS (T.InS (T.InS (T.InS (T.InS (T.InS T.InZ)))))))

-- TODO: do this on the Haskell side (also this doesn't respect the context)
instance Show (T.:⊢) where
    show Ltrue  = "true"
    show Lfalse = "false"
    show Land   = "and"
    show Lor    = "or"
    show Lnot   = "not"
    show LA     = "A"
    show LB     = "B"
    show LC     = "C"
    show (T.V _) = "unknown"
    show ((T.:·:) t  u) = "(" ++ show t ++ " " ++ show u ++ ")"

(@) :: Checker Term -> Checker Term -> Checker Term
(@) l r = do
    l1 <- l 
    l2 <- r
    ctx <- ask
    case T.mkApp ctx l1 l2 of
        Nothing -> error $ "App: type checking of " ++ show l1 ++ " and " ++ show l2 ++ " failed."
        Just (_, t) -> return t

type Sequent = P.Sequent

instance Show P.Sequent where
    show (a P.:⇒ c) = show a ++ " ⇒ " ++ show c

type Step = P.Step

pattern Assume :: [P.Sequent] -> P.Sequent -> P.Step
pattern Assume prem s = P.MkAssume prem s

pattern Step :: [P.Sequent] -> ProofRule -> [P.Step] -> P.Args -> P.Step
pattern Step prem rule steps args = P.MkStep prem rule steps args
{-# COMPLETE Assume, Step #-}

-- TODO: unsafe
mkSequent :: Term -> Checker Sequent
mkSequent t = do
    ctx <- ask
    if T.getSort ctx t == T.𝔹 then
        return $ (P.:⇒) {P.antecedent = [], P.conclusion = t}
    else error "mkSequent: wrong sort" 

-- Restricted version with no antecedent
mkAssume :: [Term] -> Term ->  Checker P.Step
mkAssume prem t = do
    ctx <- ask
    prems <- mapM mkSequent prem
    case P.mkAssume ctx t prems of
        Just step -> return step
        Nothing -> error "mkAssume: term not in premisses"

-- TODO: highly unsafe
mkStep :: [Term] -> ProofRule -> [Step] -> Checker Step 
mkStep prem rule input = do
    prems <- mapM mkSequent prem
    return $ P.MkStep prems rule input [] 