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
            lC
           )  where

import Control.Monad.Reader
-- import Control.Monad.Trans.Class (lift)
import qualified Core.Terms as T

type Term = (T.:⊢)

pattern (:·:) :: Term -> Term -> Term
pattern (:·:) t1 t2 = t1 T.:·: t2

type Checker = ReaderT T.Signature IO

runChecker :: Checker a -> IO a
runChecker c = runReaderT c T.sig 

mkCnst :: Int -> Checker Term
mkCnst i = do
    ctx <- ask
    case (T.mkCnst ctx i) of
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
        Nothing -> error "App: type checking error!" -- TODO: use IO exceptions
        Just (_, t) -> return t
