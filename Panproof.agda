module Panproof where

open import Haskell.Prelude

infixr 30 _:→_

data Sort : Set where
    𝔹 : Sort
    _:→_ : Sort → Sort → Sort
{-# COMPILE AGDA2HS Sort deriving (Show) #-}

data Signature : Set where
  MkSignature : List (Sort × String) → Signature
{-# COMPILE AGDA2HS Signature newtype #-}

getSig : Signature → List (Sort × String) 
getSig (MkSignature s) = s
{-# COMPILE AGDA2HS getSig #-}

exmplSig : Signature
exmplSig = MkSignature
    ((𝔹 , "a") ∷ (𝔹 , "b") ∷ (𝔹 , "c") ∷ 
     (𝔹 , "true") ∷ (𝔹 , "false") ∷ (𝔹 :→ 𝔹 , "not") ∷ (𝔹 :→ 𝔹 :→ 𝔹 , "and") ∷ (𝔹 :→ 𝔹 :→ 𝔹 , "or") ∷ [])
{-# COMPILE AGDA2HS exmplSig #-}

infixl 30 _:·:_
data PreTerm : Set where
  Var : Nat → PreTerm
  _:·:_ : PreTerm → PreTerm → PreTerm
{-# COMPILE AGDA2HS PreTerm deriving (Show) #-}

testPreTerm : PreTerm
testPreTerm = Var 6 :·: Var 0 :·: Var 1
{-# COMPILE AGDA2HS testPreTerm #-}

-- Typing relation
data _⊢t_⦂_ : Signature → PreTerm → Sort → Set where
  ⊢Var : ∀ {Γ n S}
    → ⦃ n<Γ : IsTrue (n < lengthNat (getSig Γ))⦄
    → fst ((getSig Γ) !!ᴺ n) ≡ S
    → Γ ⊢t Var n ⦂ S

  ⊢App : ∀ {Γ t₁ S₁ t₂ S₂}
    → Γ ⊢t t₁ ⦂ S₁ :→ S₂
    → Γ ⊢t t₂ ⦂ S₁
    ----------------------
    → Γ ⊢t t₁ :·: t₂ ⦂ S₂

record Term (@0 Γ : Signature) : Set where 
  constructor MkTerm
  field
    term : PreTerm
    sort : Sort
    @0 typing : (Γ ⊢t term ⦂ sort)
open Term public
{-# COMPILE AGDA2HS Term deriving (Show) #-}

-- testTerm : Term
-- testTerm = record {sig = exmplSig; term = testPreTerm; sort = 𝔹;
--    typing = ⊢App (⊢App (⊢Var refl) (⊢Var refl)) (⊢Var refl)}
-- {-# COMPILE AGDA2HS testTerm #-}

testTerm : (Term exmplSig)
testTerm = record {term = testPreTerm; sort = 𝔹;
   typing = ⊢App (⊢App (⊢Var refl) (⊢Var refl)) (⊢Var refl)}  
{-# COMPILE AGDA2HS testTerm #-}

useEq : {x y : Bool} → y ≡ x → IsTrue x → IsTrue y
useEq {True} {True} eq is = IsTrue.itsTrue

typecheck : (Γ : Signature) → PreTerm → Maybe (Term Γ)
typecheck gamma (Var n) = if n < lengthNat (getSig gamma) then
    (λ ⦃ n<gamma ⦄ → Just (MkTerm (Var n) (fst (_!!ᴺ_ (getSig gamma) n ⦃ useEq n<gamma IsTrue.itsTrue ⦄)) (⊢Var ⦃ useEq n<gamma IsTrue.itsTrue ⦄ refl)))
  else Nothing
typecheck gamma (t₁ :·: t₂) = typecheck gamma t₁ >>= (λ s₁ → typecheck gamma t₂ >>= λ s₂ →
  Just (MkTerm ((term s₁) :·: (term s₂)) {!   !} (⊢App (typing {! s₁ !}) (typing s₂)))) 

-- typecheck : Signature → PreTerm → Maybe Term 
-- typecheck gamma (Var n) = if n < lengthNat (getSig gamma) then
--     (λ ⦃ n<gamma ⦄ → Just (MkTerm gamma (Var n) (fst (_!!ᴺ_ (getSig gamma) n ⦃ useEq n<gamma IsTrue.itsTrue ⦄)) (⊢Var ⦃ useEq n<gamma IsTrue.itsTrue ⦄ refl)))
--   else Nothing
-- typecheck gamma (t₁ :·: t₂) = typecheck gamma t₁ >>= (λ s₁ → typecheck gamma t₂ >>= λ s₂ →
--   Nothing) --Just (MkTerm gamma t {!   !} (⊢App (typing {!  s₁ !}) {!   !}))) 

{-# COMPILE AGDA2HS typecheck #-}
