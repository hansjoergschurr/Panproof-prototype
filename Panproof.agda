module Panproof where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
-- TODO: I should not import this here
open import Haskell.Prim

-- Proof helpers
useEq : {x y : Bool} → y ≡ x → IsTrue x → IsTrue y
useEq {True} {True} eq is = IsTrue.itsTrue


infixr 30 _:→_

data Sort : Set where
    𝔹 : Sort
    _:→_ : Sort → Sort → Sort
{-# COMPILE AGDA2HS Sort deriving (Show) #-}

isFunSort : Sort → Bool
isFunSort 𝔹 = False
isFunSort (_ :→ _) = True
{-# COMPILE AGDA2HS isFunSort #-}

codomainSort : (s : Sort) → ⦃ @0 h₁ : ((isFunSort s) ≡ True) ⦄ → Sort
codomainSort (s :→ s₁) = s₁
{-# COMPILE AGDA2HS codomainSort #-}

domainSort : (s : Sort) → ⦃ @0 h₁ : ((isFunSort s) ≡ True) ⦄ → Sort
domainSort (s :→ s₁) = s
{-# COMPILE AGDA2HS domainSort #-}

instance
  isSortEq : Eq Sort
  isSortEq ._==_ 𝔹 𝔹 = True
  isSortEq ._==_ (s₁ :→ t₁) (s₂ :→ t₂) = s₁ == s₂ && t₁ == t₂
  isSortEq ._==_ _ _ = False
{-# COMPILE AGDA2HS isSortEq #-}

instance
  isLawfulSortEq : IsLawfulEq Sort
  isLawfulSortEq .isEquality 𝔹 𝔹 = refl
  isLawfulSortEq .isEquality (x :→ x₁) (y :→ y₁) with x == y in eq
  ... | False = λ h → exFalso (equality' x y (cong (λ {𝔹 → 𝔹
                                                     ; (p :→ p₁) → p}) h)) eq
  isLawfulSortEq .isEquality 𝔹 (y :→ y₁) = λ ()
  isLawfulSortEq .isEquality (x :→ x₁) 𝔹 = λ ()

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

typecheck : (Γ : Signature) → PreTerm → Maybe (Term Γ)
typecheck gamma (Var n) = if n < lengthNat (getSig gamma) then
    (λ ⦃ n<gamma ⦄ → Just (MkTerm (Var n) (fst (_!!ᴺ_ (getSig gamma) n ⦃ useEq n<gamma IsTrue.itsTrue ⦄)) (⊢Var ⦃ useEq n<gamma IsTrue.itsTrue ⦄ refl)))
  else Nothing
typecheck gamma (t₁ :·: t₂) = typecheck gamma t₁ >>=
                      (λ s₁ → typecheck gamma t₂ >>= λ s₂ →
  if isFunSort (sort s₁) then
    if {! codomainSort (sort s₁)  !} == {!   !} then {!   !}
     else Nothing else Nothing)
  -- Just (MkTerm ((term s₁) :·: (term s₂)) {!   !} (⊢App (typing {! s₁ !}) (typing s₂)))) 

-- typecheck : Signature → PreTerm → Maybe Term 
-- typecheck gamma (Var n) = if n < lengthNat (getSig gamma) then
--     (λ ⦃ n<gamma ⦄ → Just (MkTerm gamma (Var n) (fst (_!!ᴺ_ (getSig gamma) n ⦃ useEq n<gamma IsTrue.itsTrue ⦄)) (⊢Var ⦃ useEq n<gamma IsTrue.itsTrue ⦄ refl)))
--   else Nothing
-- typecheck gamma (t₁ :·: t₂) = typecheck gamma t₁ >>= (λ s₁ → typecheck gamma t₂ >>= λ s₂ →
--   Nothing) --Just (MkTerm gamma t {!   !} (⊢App (typing {!  s₁ !}) {!   !}))) 

{-# COMPILE AGDA2HS typecheck #-}
