{-# OPTIONS_GHC -Wall #-}

module Main where

import API
import Control.Monad.Trans.Class (lift)

termTest :: Checker ()
termTest = do
    t <- land @ lA @ lB
    lift $ print t

main :: IO ()
main = runChecker termTest
