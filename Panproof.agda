module Panproof where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Extra.Dec
-- TODO: I should not import this here
open import Haskell.Prim

-- Proof helpers
useEq : {x y : Bool} → y ≡ x → IsTrue x → IsTrue y
useEq {True} {True} eq is = IsTrue.itsTrue

infixr 30 _:→_

data Sort : Set where
    𝔹 : Sort
    _:→_ : Sort → Sort → Sort
{-# COMPILE AGDA2HS Sort deriving (Show, Eq) #-}

postulate instance isSortEq : Eq Sort
postulate instance isSortLawfulEq : IsLawfulEq Sort

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

{- This doesn't pass the termination checker.  That seems common.  For example, here:
https://github.com/sarajuhosova/agda2hs-playground/blob/master/agda/TypeCheck/Type.agda
a TERMINATING annotation is used.  Using derive + postulate seems more close to idiomatic
Haskell code -}
-- instance
--   isSortEq : Eq Sort
--   isSortEq ._==_ 𝔹 𝔹 = True
--   isSortEq ._==_ (s₁ :→ t₁) (s₂ :→ t₂) = s₁ == s₂ && t₁ == t₂
--   isSortEq ._==_ _ _ = False
-- {-# COMPILE AGDA2HS isSortEq #-}

-- instance
--   isLawfulSortEq : IsLawfulEq Sort
--   isLawfulSortEq .isEquality 𝔹 𝔹 = refl
--   isLawfulSortEq .isEquality (x₁ :→ x₂) (y₁ :→ y₂) with x₁ == y₁ in eq₁
--   ... | True = mapReflects ((λ h → cong₂ _:→_ (equality x₁ y₁ eq₁) h)) (cong (λ {𝔹 → 𝔹 ; (p :→ s) → s})) (isEquality x₂ y₂)
--   ... | False = λ h → exFalso (equality' x₁ y₁ (cong (λ {𝔹 → 𝔹 ; (p :→ s) → p}) h)) eq₁
--   isLawfulSortEq .isEquality 𝔹 (_ :→ _) = λ ()
--   isLawfulSortEq .isEquality (_ :→ _) 𝔹 = λ ()

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

testTerm : (Term exmplSig)
testTerm = record {term = testPreTerm; sort = 𝔹;
   typing = ⊢App (⊢App (⊢Var refl) (⊢Var refl)) (⊢Var refl)}  
{-# COMPILE AGDA2HS testTerm #-}

typecheck : (Γ : Signature) → PreTerm → Maybe (Term Γ)
typecheck ctx (Var n) = if n < lengthNat (getSig ctx) then
    (λ ⦃ n<ctx ⦄ → Just (MkTerm (Var n) (fst (_!!ᴺ_ (getSig ctx) n ⦃ useEq n<ctx IsTrue.itsTrue ⦄)) (⊢Var ⦃ useEq n<ctx IsTrue.itsTrue ⦄ refl)))
  else Nothing
typecheck ctx (t₁ :·: t₂) = do
  s₁ ← typecheck ctx t₁
  s₂ ← typecheck ctx t₂
  case (sort s₁) of λ where
    (u₁ :→ u₂) ⦃ refl ⦄ → do
      if (sort s₂) == u₁ then (λ ⦃ h ⦄ → Just (MkTerm ((term s₁) :·: (term s₂))
                                                       u₂
                                                       (⊢App (typing s₁) (subst (λ p → ctx ⊢t term s₂ ⦂ p) (equality (sort s₂) u₁ h) (typing s₂))))) 
                          else Nothing
    _ → Nothing
{-# COMPILE AGDA2HS typecheck #-}
