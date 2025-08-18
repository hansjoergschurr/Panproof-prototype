module Core.Proofs where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Bool
open import Haskell.Extra.Dec
open import Haskell.Extra.Sigma
open import Haskell.Extra.Refinement hiding (proof)

open import Core.Terms

record Sequent (@0 Γ : Signature) : Set where
  constructor _:⇒_
  field
    antecedent : List (Γ :⊢ 𝔹)
    conclusion : (Γ :⊢ 𝔹) 
open Sequent public
{-# COMPILE AGDA2HS Sequent deriving (Eq, Ord) #-}

postulate instance isSequentEq : ∀ {@0 Γ : Signature} → Eq (Sequent Γ)
postulate instance isSequentLawfulEq : ∀ {@0 Γ : Signature} → IsLawfulEq (Sequent Γ)

-- TODO: do I need to define this, or does it exist somewhere?
data _∈_ : {@0 Γ : Signature} → Sequent Γ → List (Sequent Γ) → Set where
  ∈H : ∀ {@0 Γ} {t x : Sequent Γ} {ts : List (Sequent Γ)} → @0 t ≡ x → _∈_ {Γ} t (x ∷ ts)
  ∈T : ∀ {@0 Γ} {t x : Sequent Γ} {ts : List (Sequent Γ)} → _∈_ {Γ} t ts → _∈_ {Γ} t (x ∷ ts)  

Args : (@0 Γ : Signature) → Set
Args Γ = List (Γ :⊢ 𝔹) -- TODO: this should be heterogenous
{-# COMPILE AGDA2HS Args #-}

data Step (@0 Γ : Signature) (@0 prem : List (Sequent Γ)) : Set 

-- Abstract Proof checker to use in proof of equivalence
checkStep : {@0 Γ : Signature} {@0 prem : List (Sequent Γ)} → Maybe (Step Γ prem) → Maybe (Sequent Γ) 
-- Reimplementation of mapM for our case to make the terminatino checker happy.
checkMap : {@0 Γ : Signature} {@0 prem : List (Sequent Γ)} → List (Step Γ prem) → Maybe (List (Sequent Γ))

data ProofRule (@0 Γ : Signature) : Set where
  Axiom :
      (name  : String)
      (infer : (List (Sequent Γ) → Args Γ → Maybe (Sequent Γ)))
    ---------------------------------------------------
    → ProofRule Γ

  Rule :
      (name      : String)
    → (infer     : (List (Sequent Γ) → Args Γ → Maybe (Sequent Γ)))
    → (elaborate : (prems : List (Sequent Γ)) → Args Γ → Maybe (Step Γ prems))
    → (@0 proof  : ((prem : List (Sequent Γ)) → (args : Args Γ) →
                    (infer prem args) ≡ (checkStep (elaborate prem args))))
    ---------------------------------------------------
    → ProofRule Γ
{-# COMPILE AGDA2HS ProofRule #-}

-- We index by the premisses, but also store it in each node for the API
data Step Γ prem where
  MkAssume : 
      (prem' : List (Sequent Γ))
    → @0 prem ≡ prem'
    → (s : Sequent Γ)
    → @0 s ∈ prem
    → Step Γ prem

  MkStep :
      (prem' : List (Sequent Γ))
    → @0 prem ≡ prem'
    → ProofRule Γ 
    → List (Step Γ prem)
    → Args Γ
    → Step Γ prem
{-# COMPILE AGDA2HS Step #-}

checkMap [] = Just []
checkMap (s ∷ ss) = do
  ss' ← checkMap ss 
  s' ← checkStep (Just s)
  Just (s' ∷ ss')

checkStep {Γ} Nothing = Nothing
checkStep {Γ} (Just (MkAssume _ _ s _)) = Just s
checkStep {Γ} (Just (MkStep _ _ (Axiom _ infer)            prem args)) = checkMap prem >>= λ p → infer p args
checkStep {Γ} (Just (MkStep _ _ (Rule _ infer elaborate _) prem args)) = checkMap prem >>= λ p → infer p args

-------------------------------------
-- Safe API functions
-------------------------------------

lookupInParam : ∀ {@0 Γ : Signature} → (s : Sequent Γ) → (prem : List (Sequent Γ)) → Dec (_∈_ {Γ} s prem)
lookupInParam t [] = False ⟨ (λ ()) ⟩
lookupInParam {Γ} t (x ∷ prem) =
    if (isSequentEq {Γ} Eq.== t) x then 
      (λ ⦃ h ⦄ → True ⟨ (∈H {Γ} (equality t x h)) ⟩)
    else (λ ⦃ h ⦄ → case lookupInParam {Γ} t prem of λ where
      (False ⟨ ¬p ⟩) → False ⟨ notPossible h ¬p ⟩
      (True ⟨ p ⟩) → True ⟨ (∈T p) ⟩
    )
    where
      @0 notPossible : ((t == x) ≡ False) → (t ∈ prem → ⊥) → t ∈ (x ∷ prem) → ⊥ 
      notPossible h ¬p (∈H refl) = nequality t x h refl
      notPossible h ¬p (∈T p) = ¬p p
{-# COMPILE AGDA2HS lookupInParam #-}

mkAssume : ∀ {@0 S : Sort} (Γ : Signature) → (t : Γ :⊢ S) → (prem : List (Sequent Γ)) → Maybe (Step Γ prem)
mkAssume {S} ctx t prems = case (getSort ctx t) of λ where
  (𝔹 ⟨ refl ⟩) → case lookupInParam ([] :⇒ t) prems of (λ where
      (True ⟨ t∈prems ⟩) → Just (MkAssume prems refl ([] :⇒ t) t∈prems)
      _ → Nothing
    )
  _ → Nothing
{-# COMPILE AGDA2HS mkAssume #-}
