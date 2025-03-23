module Panproof where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Bool
open import Haskell.Extra.Dec
open import Haskell.Extra.Sigma

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

Signature : Set
Signature = List (Sort × String) 
{-# COMPILE AGDA2HS Signature #-}

data Idx : Set where
  IH : Idx
  IT : Idx → Idx
{-# COMPILE AGDA2HS Idx (Show) #-}

-- Sort lookup evidence
data _[_]=_ : Signature → Idx → Sort → Set where
  IsHere : ∀ {Γ s l} → ((s , l) ∷ Γ) [ IH ]= s
  IsThere : ∀ {Γ idx s e} → Γ [ idx ]= s → (e ∷ Γ) [ IT idx ]= s

lookupSort : ∀ (ctx : Signature) (n : Idx) → Maybe Sort
lookupSort [] _ = Nothing
lookupSort ((s , _) ∷ _) IH = Just s
lookupSort (_ ∷ ctx) (IT n) = lookupSort ctx n
{-# COMPILE AGDA2HS lookupSort #-}

lookupSortCorrect : ∀ (ctx : Signature) (n : Idx)
                    → ⦃ h : IsJust (lookupSort ctx n) ⦄
                    → ctx [ n ]= fromJust (lookupSort ctx n) {h}
lookupSortCorrect (x ∷ ctx) IH = IsHere
lookupSortCorrect (x ∷ ctx) (IT n) = IsThere (lookupSortCorrect ctx n)

exmplSig : Signature
exmplSig = (𝔹 , "a") ∷ (𝔹 , "b") ∷ (𝔹 , "c") ∷ 
     (𝔹 , "true") ∷ (𝔹 , "false") ∷ (𝔹 :→ 𝔹 , "not") ∷ (𝔹 :→ 𝔹 :→ 𝔹 , "and") ∷ (𝔹 :→ 𝔹 :→ 𝔹 , "or") ∷ []
{-# COMPILE AGDA2HS exmplSig #-}

infixl 30 _:·:_
data Term : Set where
  Var : Idx → Term
  _:·:_ : Term → Term → Term
{-# COMPILE AGDA2HS Term deriving (Show) #-}

pattern la = Var IH 
pattern lb = Var (IT IH) 
pattern land = Var (IT (IT (IT (IT (IT (IT IH)))))) 

testTerm : Term
testTerm = land :·: la :·: lb
{-# COMPILE AGDA2HS testTerm #-}

-- Typing relation
data _⊢_⦂_ : Signature → Term → Sort → Set where
  ⊢Var : ∀ {Γ n S}
    → ⦃ Γ[n]=S : Γ [ n ]= S ⦄
    → Γ ⊢ Var n ⦂ S

  ⊢App : ∀ {Γ t₁ S₁ t₂ S₂}
    → Γ ⊢ t₁ ⦂ S₁ :→ S₂
    → Γ ⊢ t₂ ⦂ S₁
    ----------------------
    → Γ ⊢ t₁ :·: t₂ ⦂ S₂

getSort : (ctx : Signature) → (t : Term) → Maybe Sort
getSort ctx (Var n) = lookupSort ctx n
getSort ctx (t₁ :·: t₂) = do
  s₁ ← getSort ctx t₁
  s₂ ← getSort ctx t₂
  case s₁ of λ where
    (u₁ :→ u₂) ⦃ refl ⦄ → if s₂ == u₁ then Just u₂ else Nothing
    _ → Nothing
{-# COMPILE AGDA2HS getSort #-}

getSortCorrect : (ctx : Signature) (t : Term)
               → ⦃ h : IsJust (getSort ctx t) ⦄
               → ctx ⊢ t ⦂ (fromJust (getSort ctx t) { h })
getSortCorrect ctx (Var n) ⦃ h ⦄ = ⊢Var ⦃ lookupSortCorrect ctx n ⦄
getSortCorrect ctx (t₁ :·: t₂) ⦃ h ⦄ = 
  let h₁ = getSortCorrect ctx t₁
      h₂ = getSortCorrect ctx t₂
  in 
  ⊢App {!h₁ ⦃ ? ⦄ !} (h₂ ⦃ {!   !} ⦄)

-- getSort : (ctx : Signature) → (t : Term) → Maybe (Σ[ s ∈ Sort ] ctx ⊢ t ⦂ s)
-- getSort ctx (Var n) = Nothing {- if n < lengthNat ctx then
--     (λ where ⦃ n<ctx ⦄ → Just ((fst (_!!ᴺ_ ctx n ⦃ useEq n<ctx IsTrue.itsTrue ⦄)) , (⊢Var ⦃ useEq n<ctx IsTrue.itsTrue ⦄ refl)))
--   else Nothing -}
-- getSort ctx (t₁ :·: t₂) = Nothing -- do
--   -- s₁ ← getSort ctx t₁
--   -- s₂ ← getSort ctx t₂
--   -- case (sort s₁) of λ where
--   --   (u₁ :→ u₂) ⦃ refl ⦄ → do
--   --     if (sort s₂) == u₁ then (λ ⦃ h ⦄ → Just (MkTerm ((term s₁) :·: (term s₂))
--   --                                                      u₂
--   --                                                      (⊢App (typing s₁) (subst (λ p → ctx ⊢t term s₂ ⦂ p) (equality (sort s₂) u₁ h) (typing s₂))))) 
--   --                         else Nothing
--   --   _ → Nothing
-- {-# COMPILE AGDA2HS getSort #-}
