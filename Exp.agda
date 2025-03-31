module Exp where

open import Haskell.Prelude
open import Haskell.Law
open import Haskell.Extra.Sigma

data Foo (@0 i : Int) : Set where
    Bar : Foo i
{-# COMPILE AGDA2HS Foo #-}

-- record Baz (a : Set) (b : @0 a → Set) : Set where
--   constructor _⟫_
--   field
--     bazfst : a
--     @0 bazsnd : b bazfst
-- open Baz public

-- {-# COMPILE AGDA2HS Σ tuple #-}
-- test : (i : Int) → (Int ⟫ (λ x → i ≡ x))
-- test i = i , ?
-- {-# COMPILE AGDA2HS test #-}

