module Core.Proofs where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality
open import Haskell.Law.Bool
open import Haskell.Extra.Dec
open import Haskell.Extra.Sigma

open import Core.Terms

record Sequent (@0 Γ : Signature) : Set where
  constructor _:⇒_
  field
    antecedent : List (Γ :⊢ 𝔹)
    conclusion : (Γ :⊢ 𝔹) 
    -- @0 {antecedentTyped} : All (λ {t → (getSort Γ t) ≡ (Just 𝔹)}) antecedent
    -- @0 {conclusionTyped} : getSort Γ conclusion ≡ Just 𝔹 
open Sequent public
{-# COMPILE AGDA2HS Sequent #-}

-- TODO: do I need to define this, or does it exist somewhere?
data _∈_ : {Γ : Signature} → Sequent Γ → List (Sequent Γ) → Set where
  ∈H : ∀ {Γ t ts} → _∈_ {Γ} t (t ∷ ts)
  ∈T : ∀ {Γ t x ts} → _∈_ {Γ} t ts → _∈_ {Γ} t (x ∷ ts)  

Args : (@0 Γ : Signature) → Set
Args Γ = List (Γ :⊢ 𝔹) -- TODO: this should be heterogenous
{-# COMPILE AGDA2HS Args #-}

data Step (@0 Γ : Signature) (@0 prem : List (Sequent Γ)) : Set 

-- Abstract Proof checker to use in proof of equivalence
checkStep : {@0 Γ : Signature} {@0 prem : List (Sequent Γ)} → Maybe (Step Γ prem) → Maybe (Sequent Γ) 
-- Reimplementation of mapM for our case to make the terminatino checker happy.
checkMap : {@0 Γ : Signature} {@0 prem : List (Sequent Γ)} → List (Step Γ prem) → Maybe (List (Sequent Γ))

data ProofRule (@0 Γ : Signature) : Set where
  Axiom : (check : (List (Sequent Γ) → Args Γ → Maybe (Sequent Γ))) → ProofRule Γ
  Rule :
      (check     : (List (Sequent Γ) → Args Γ → Maybe (Sequent Γ)))
    → (elaborate : (prems : List (Sequent Γ)) → Args Γ → Maybe (Step Γ prems))
    → (@0 proof : ((prem : List (Sequent Γ)) → (args : Args Γ) →
                   (check prem args) ≡ (checkStep (elaborate prem args))))
    ---------------------------------------------------
    → ProofRule Γ
{-# COMPILE AGDA2HS ProofRule #-}

data Step Γ prem where
  MkAssume : 
      (s : Sequent Γ)
    → @0 s ∈ prem
    → Step Γ prem

  MkStep :
      ProofRule Γ 
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
checkStep {Γ} (Just (MkAssume s _)) = Just s
checkStep {Γ} (Just (MkStep (Axiom check)            prem args)) = checkMap prem >>= λ p → check p args
checkStep {Γ} (Just (MkStep (Rule check elaborate _) prem args)) = checkMap prem >>= λ p → check p args

-------------------------------------
-- Some Axioms (a random collection)
-------------------------------------

axTrue : ProofRule sig
axTrue = Axiom (λ _ _ → Just ([] :⇒ ltrue))
{-# COMPILE AGDA2HS axTrue #-}

axAssume : ProofRule sig
axAssume = Axiom check
  where check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
        check [] (t ∷ []) = Just ((t ∷ []) :⇒ t)
        check _ _ = Nothing
{-# COMPILE AGDA2HS axAssume #-}

axAndI : ProofRule sig
axAndI = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check ((a1 :⇒ x) ∷ (a2 :⇒ y) ∷ []) _ = Just ((a1 ++ a2) :⇒ (land :·: x :·: y))
    check _ _ = Nothing
{-# COMPILE AGDA2HS axAndI #-}

axAndE1 : ProofRule sig
axAndE1 = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ (land :·: x :·: y) ∷ []) _ = Just (a :⇒ x)
    check _ _ = Nothing
{-# COMPILE AGDA2HS axAndE1 #-}

axAndE2 : ProofRule sig
axAndE2 = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ (land :·: x :·: y) ∷ []) _ = Just (a :⇒ y)
    check _ _ = Nothing
{-# COMPILE AGDA2HS axAndE2 #-}

axNotnotI : ProofRule sig
axNotnotI = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ f ∷ []) _ = Just (a :⇒ lnot :·: (lnot :·: f))
    check _ _ = Nothing
{-# COMPILE AGDA2HS axNotnotI #-}

axNotnotE : ProofRule sig
axNotnotE = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ lnot :·: (lnot :·: f) ∷ []) _ = Just (a :⇒ f)
    check _ _ = Nothing
{-# COMPILE AGDA2HS axNotnotE #-}

axOrI1 : ProofRule sig
axOrI1 = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ f ∷ []) (g ∷ []) = Just (a :⇒ lor :·: f :·: g )
    check _ _ = Nothing
{-# COMPILE AGDA2HS axOrI1 #-}

axOrI2 : ProofRule sig
axOrI2 = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ g ∷ []) (f ∷ []) = Just (a :⇒ lor :·: f :·: g )
    check _ _ = Nothing
{-# COMPILE AGDA2HS axOrI2 #-}

axOrE : ProofRule sig
axOrE = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (        a :⇒ lor :·: f :·: g ∷ 
           (f₁ ∷ a₁) :⇒ c₁ ∷
           (g₁ ∷ a₂) :⇒ c₂ ∷ []) _ = 
      if f == f₁ && g == g₁ && a == a₁ && a == a₂ && c₁ == c₂ then
        Just (a :⇒ c₁)
      else
        Nothing
    check _ _ = Nothing
{-# COMPILE AGDA2HS axOrE #-}

axOrFalseE : ProofRule sig
axOrFalseE = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ lfalse ∷ []) (f ∷ []) = Just (a :⇒ f)
    check _ _ = Nothing
{-# COMPILE AGDA2HS axOrFalseE #-}

axNotE : ProofRule sig
axNotE = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a₁ :⇒ f₁ ∷ a₂ :⇒ lnot :·: f₂ ∷ []) (f ∷ []) =
       if a₁ == a₂ && f₁ == f₂ then Just (a₁ :⇒ lfalse) else Nothing
    check _ _ = Nothing
{-# COMPILE AGDA2HS axNotE #-}

axNegI : ProofRule sig
axNegI = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check ((f ∷ a) :⇒ lfalse ∷ []) _ = Just (a :⇒ f)
    check _ _ = Nothing
{-# COMPILE AGDA2HS axNegI #-}

axPBC : ProofRule sig
axPBC = Axiom check
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (((lnot :·: f) ∷ a) :⇒ lfalse ∷ []) _ = Just (a :⇒ f)
    check _ _ = Nothing
{-# COMPILE AGDA2HS axPBC #-}

ruleAndE3 : ProofRule sig
ruleAndE3 = Rule check elaborate proof
  where
    check : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    check (a :⇒ (land :·: f :·: (land :·: g :·: u)) ∷ []) ea = Just (a :⇒ u)
    check _ _ = Nothing

    elaborate : (prems : List (Sequent sig)) → Args sig → Maybe (Step sig prems)
    elaborate (a :⇒ (land :·: f :·: (land :·: g :·: u)) ∷ []) _ =
      let p = (a :⇒ (land :·: f :·: (land :·: g :·: u))) in
       Just (MkStep axAndE2 (MkStep axAndE2 (MkAssume p ∈H ∷ []) [] ∷ []) [])
    elaborate _ _ = Nothing

    @0 proof : (prem : List (Sequent sig)) → (args : Args sig) → (check prem args) ≡ (checkStep (elaborate prem args))
    proof [] a                                                                      = refl
    proof ((_ :⇒ (land :·: f :·: (land :·: g :·: u))) ∷ [])    _                    = refl
    proof ((_ :⇒ V x) ∷ _)                                   _                      = refl
    proof ((_ :⇒ (V x :·: _))                           ∷ _) _                      = refl
    proof ((_ :⇒ (V (InS (InS (InS (InS x)))) :·: _ :·: _)) ∷ _) _                  = refl
    proof ((_ :⇒ (_ :·: _ :·: _ :·: _)) ∷ _)                   _                    = refl
    proof ((_ :⇒ (lor :·: _ :·: _)) ∷ _)                  _                         = refl
    proof ((_ :⇒ (land :·: _ :·: V x)) ∷ _)                  _                      = refl
    proof ((_ :⇒ (land :·: _ :·: (V x :·: _))) ∷ _)          _                      = refl
    proof ((_ :⇒ (land :·: _ :·: (lor :·: _ :·: _))) ∷ _)       _                   = refl
    proof ((_ :⇒ (land :·: _ :·: (V (InS (InS (InS (InS x)))) :·: _ :·: _))) ∷ _) _ = refl
    proof ((_ :⇒ (land :·: _ :·: (_ :·: _ :·: _ :·: _))) ∷ _)  _                    = refl
    proof ((_ :⇒ (land :·: _ :·: (land :·: _ :·: _))) ∷ _ ∷ _) _                    = refl
{-# COMPILE AGDA2HS ruleAndE3 #-}

