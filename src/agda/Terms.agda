module Terms where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Bool
open import Haskell.Extra.Dec
open import Haskell.Extra.Sigma
open import Haskell.Extra.Refinement

infixr 30 _:→_

data Sort : Set where
    𝔹 : Sort
    _:→_ : Sort → Sort → Sort
{-# COMPILE AGDA2HS Sort deriving (Show, Eq) #-}

postulate instance isSortEq : Eq Sort
postulate instance isSortLawfulEq : IsLawfulEq Sort

Signature : Set
Signature = List Sort
{-# COMPILE AGDA2HS Signature deriving (Eq) #-}

infix  4 _:∋_

data _:∋_ : @0 Signature → @0 Sort → Set where

  InZ : ∀ {@0 Γ A}
      ---------
    → A ∷ Γ :∋ A

  InS : ∀ {@0 Γ A B}
    → Γ :∋ A
      ---------
    → B ∷ Γ :∋ A

{-# COMPILE AGDA2HS _:∋_ deriving (Show, Eq) #-}

postulate instance is:∋Eq : ∀ {Γ x} → Eq (Γ :∋ x)
postulate instance is:∋LawfulEq : ∀ {Γ x} → IsLawfulEq (Γ :∋ x)

lookupIdx : (Γ : Signature) {@0 s : Sort} → (Γ :∋ s) → Sort
lookupIdx (x ∷ ctx) InZ = x 
lookupIdx (x ∷ ctx) (InS idx) = lookupIdx ctx idx
{-# COMPILE AGDA2HS lookupIdx #-}

lookupIdxCorrect : {Γ : Signature} {S : Sort} → (idx : Γ :∋ S) → lookupIdx Γ idx ≡ S
lookupIdxCorrect {x ∷ Γ} InZ = refl
lookupIdxCorrect {x ∷ Γ} (InS idx) = lookupIdxCorrect idx

infixl 500 _:·:_

data _:⊢_ : @0 Signature → @0 Sort → Set where
  V : ∀ {@0 Γ S}
   → Γ :∋ S
   → Γ :⊢ S

  _:·:_ : ∀ {@0 Γ S T}
   → Γ :⊢ (S :→ T) 
   → Γ :⊢ S 
   → Γ :⊢ T
{-# COMPILE AGDA2HS _:⊢_ deriving (Show, Eq) #-}

postulate instance isTermEq : ∀ {Γ S} → Eq (Γ :⊢ S)
postulate instance isTermLawfulEq : ∀ {Γ S} →  IsLawfulEq (Γ :⊢ S)

sig : Signature
sig = 𝔹 ∷ 𝔹 ∷ 𝔹 :→ 𝔹 :→ 𝔹 ∷ 𝔹 :→ 𝔹 :→ 𝔹 ∷ 𝔹 :→ 𝔹 ∷ 𝔹 ∷ 𝔹 ∷ 𝔹 ∷ []
{-# COMPILE AGDA2HS sig #-}

pattern ltrue  = V InZ
pattern lfalse = V (InS InZ)
pattern land   = V (InS (InS InZ))
pattern lor    = V (InS (InS (InS InZ)))
pattern lnot   = V (InS (InS (InS (InS InZ))))
pattern la     = V (InS (InS (InS (InS (InS InZ)))))
pattern lb     = V (InS (InS (InS (InS (InS (InS InZ))))))
pattern lc     = V (InS (InS (InS (InS (InS (InS (InS InZ)))))))

-- Safe lookup of variables
-- TODO: proof correct (i.e. returned element is ith sort in Γ)
mkVar : (Γ : Signature) → (i : Int) → Maybe (Σ[ s ∈ Sort ] (Γ :∋ s))
mkVar [] _ = Nothing
mkVar (x ∷ xs) i = if i == 0 then Just (x , InZ) else 
  case mkVar xs (i - 1) of λ where
    Nothing → Nothing
    (Just (s , idx)) → Just (s , InS idx)
{-# COMPILE AGDA2HS mkVar #-}

getSort : ∀ (Γ : Signature) {@0 s : Sort} → Γ :⊢ s → ∃ Sort (λ t → s ≡ t)
getSort ctx (V x) = lookupIdx ctx x ⟨ sym (lookupIdxCorrect x) ⟩
getSort ctx (_:·:_ {S = su} t u) = case (getSort ctx t) of λ where -- Renaming "S" here results in su beeing used in the compiled pattern below.  Otherwise, it tries to use S. Why?
  ((s1 :→ s2) ⟨ refl ⟩) → s2 ⟨ refl ⟩
{-# COMPILE AGDA2HS getSort #-}

SubstArrowLeft : ∀ {@0 Γ : Signature} {@0 S₁ S₂ T : Sort} → @0 (S₁ ≡ S₂) → (Γ :⊢ (S₁ :→ T)) → (Γ :⊢ (S₂ :→ T))
SubstArrowLeft refl t = t
{-# COMPILE AGDA2HS SubstArrowLeft transparent #-}

mkApp : ∀ (Γ : Signature) {@0 S₁ S₂ : Sort} → Γ :⊢ S₁ → Γ :⊢ S₂ → Maybe (Σ[ s ∈ Sort ] (Γ :⊢ s))
mkApp ctx {S₂ = s₂} t₁ t₂ = case getSort ctx t₁ of λ where
    ((s₁' :→ s₃) ⟨ refl ⟩) → case getSort ctx t₂ of λ where (s₄ ⟨ refl ⟩) → if s₁' == s₄ then (λ ⦃ h ⦄ → Just (s₃ , SubstArrowLeft (equality s₁' s₂ h) t₁ :·: t₂)) else Nothing 
    (𝔹 ⟨ _ ⟩) → Nothing
{-# COMPILE AGDA2HS mkApp #-}
