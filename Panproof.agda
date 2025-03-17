module Panproof where

open import Haskell.Prelude

data Sort : Set where
    𝔹 : Sort
    To : Sort → Sort → Sort

record Signature : Set where
    inductive
    field
        parent : Maybe Signature
        cnsts : List Sort
        symbols : List String -- TODO: Assert equal size
open Signature public

-- Copaterns don't work
propLogic : Signature
propLogic = record {
    parent = Nothing;
    cnsts  = 𝔹 ∷ 𝔹 ∷ (To 𝔹 𝔹) ∷ (To (To 𝔹 𝔹) 𝔹) ∷ (To (To 𝔹 𝔹) 𝔹) ∷ [];
    symbols = "true" ∷ "false" ∷ "not" ∷ "and" ∷ "or" ∷ []
  }

exampleSig : Signature
exampleSig = record {
    parent = Just propLogic;
    cnsts  = 𝔹 ∷ 𝔹 ∷ 𝔹 ∷ [];
    symbols = "a" ∷ "b" ∷ "c" ∷ []
  }

-- Agda2Hs exports
{-# COMPILE AGDA2HS Sort #-}
{-# COMPILE AGDA2HS Signature #-}
{-# COMPILE AGDA2HS propLogic #-}
{-# COMPILE AGDA2HS exampleSig #-}
