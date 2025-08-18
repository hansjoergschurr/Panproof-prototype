module Core.Rules where

open import Haskell.Prelude
open import Haskell.Law.Eq

open import Core.Terms
open import Core.Proofs
open import Haskell.Extra.Refinement hiding (proof)


-------------------------------------
-- Some Axioms
-------------------------------------

axTrue : ProofRule sig
axTrue = Axiom "true" (λ _ _ → Just ([] :⇒ ltrue))
{-# COMPILE AGDA2HS axTrue #-}

axAssume : ProofRule sig
axAssume = Axiom "assume" infer
  where infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
        infer [] (t ∷ a) = Just ((t ∷ a) :⇒ t)
        infer _ _ = Nothing
{-# COMPILE AGDA2HS axAssume #-}

axAndI : ProofRule sig
axAndI = Axiom "andI" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer ((a1 :⇒ x) ∷ (a2 :⇒ y) ∷ []) _ = Just ((a1 ++ a2) :⇒ (land :·: x :·: y))
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axAndI #-}

axAndE1 : ProofRule sig
axAndE1 = Axiom "andE1" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ (land :·: x :·: y) ∷ []) _ = Just (a :⇒ x)
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axAndE1 #-}

axAndE2 : ProofRule sig
axAndE2 = Axiom "andE2" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ (land :·: x :·: y) ∷ []) _ = Just (a :⇒ y)
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axAndE2 #-}

axNotnotI : ProofRule sig
axNotnotI = Axiom "notnotI" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ f ∷ []) _ = Just (a :⇒ lnot :·: (lnot :·: f))
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axNotnotI #-}

axNotnotE : ProofRule sig
axNotnotE = Axiom "notnotE" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ lnot :·: (lnot :·: f) ∷ []) _ = Just (a :⇒ f)
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axNotnotE #-}

axOrI1 : ProofRule sig
axOrI1 = Axiom "orI1" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ f ∷ []) (g ∷ []) = Just (a :⇒ lor :·: f :·: g )
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axOrI1 #-}

axOrI2 : ProofRule sig
axOrI2 = Axiom "orI2" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ g ∷ []) (f ∷ []) = Just (a :⇒ lor :·: f :·: g )
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axOrI2 #-}

axOrE : ProofRule sig
axOrE = Axiom "orE" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (        a :⇒ lor :·: f :·: g ∷ 
           (f₁ ∷ a₁) :⇒ c₁ ∷
           (g₁ ∷ a₂) :⇒ c₂ ∷ []) _ =
      if f == f₁ && g == g₁ && a == a₁ && a == a₂ && c₁ == c₂ then
        Just (a :⇒ c₁)
      else
        Nothing
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axOrE #-}

axOrFalseE : ProofRule sig
axOrFalseE = Axiom "falseE" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ lfalse ∷ []) (f ∷ []) = Just (a :⇒ f)
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axOrFalseE #-}

axNotE : ProofRule sig
axNotE = Axiom "notE" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a₁ :⇒ f₁ ∷ a₂ :⇒ lnot :·: f₂ ∷ []) (f ∷ []) =
       if a₁ == a₂ && f₁ == f₂ then Just (a₁ :⇒ lfalse) else Nothing
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axNotE #-}

axNegI : ProofRule sig
axNegI = Axiom "negI" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer ((f ∷ a) :⇒ lfalse ∷ []) _ = Just (a :⇒ f)
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axNegI #-}

axPBC : ProofRule sig
axPBC = Axiom "pbc" infer
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (((lnot :·: f) ∷ a) :⇒ lfalse ∷ []) _ = Just (a :⇒ f)
    infer _ _ = Nothing
{-# COMPILE AGDA2HS axPBC #-}

ruleAndE3 : ProofRule sig
ruleAndE3 = Rule "andE3" infer elaborate proof
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ (land :·: f :·: (land :·: g :·: u)) ∷ []) ea = Just (a :⇒ u)
    infer _ _ = Nothing

    elaborate : (prems : List (Sequent sig)) → Args sig → Maybe (Step sig prems)
    elaborate (a :⇒ (land :·: f :·: (land :·: g :·: u)) ∷ []) _ =
      let p = (a :⇒ (land :·: f :·: (land :·: g :·: u))) in
       Just (MkStep (p ∷ []) refl 
                    axAndE2
                    (MkStep (p ∷ []) refl
                             axAndE2
                             (MkAssume (p ∷ []) refl p (∈H refl) ∷ []) [] ∷ []) [])
    elaborate _ _ = Nothing

    @0 proof : (prem : List (Sequent sig)) → (args : Args sig)
             → (infer prem args) ≡ (checkStep (elaborate prem args))
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

ruleOrSym : ProofRule sig
ruleOrSym = Rule "orSym" infer elaborate proof
  where
    infer : List (Sequent sig) → Args sig → Maybe (Sequent sig)
    infer (a :⇒ (lor :·: f :·: g) ∷ []) ea = Just (a :⇒ (lor :·: g :·: f))
    infer _ _ = Nothing

    elaborate : (prems : List (Sequent sig)) → Args sig → Maybe (Step sig prems)
    elaborate (a :⇒ (lor :·: f :·: g) ∷ []) _ =
      let p = (a :⇒ (lor :·: f :·: g)) in
       Just (MkStep (p ∷ []) refl
                    axOrE
                    (MkAssume (p ∷ []) refl p (∈H refl) ∷
                     MkStep (p ∷ []) refl axOrI2 (MkStep (p ∷ []) refl axAssume [] (f ∷ a) ∷ []) (g ∷ []) ∷
                     MkStep (p ∷ []) refl axOrI1 (MkStep (p ∷ []) refl axAssume [] (g ∷ a) ∷ []) (f ∷ [])
                     ∷ [])
            [])
    elaborate _ _ = Nothing

    @0 proof : (prem : List (Sequent sig)) → (args : Args sig) → (infer prem args) ≡ (checkStep (elaborate prem args))
    proof [] _ = refl
    proof p@((a :⇒ (lor :·: f :·: g)) ∷ []) _ with equality' f f refl | equality' g g refl | equality' a a refl | equality' (lor :·: g :·: f) (lor :·: g :·: f) refl
    ... | f=f | g=g | a=a | pre=pre rewrite f=f rewrite g=g rewrite a=a rewrite pre=pre = refl
    proof ((a :⇒ V x) ∷ _) args = refl
    proof ((a :⇒ (V x :·: p₁)) ∷ _) args = refl
    proof ((a :⇒ (land :·: p₂ :·: p₁)) ∷ _) args = refl
    proof ((a :⇒ (lor :·: p₂ :·: p₁)) ∷ _ ∷ b) args = refl
    proof ((a :⇒ (V (InS (InS (InS (InS x)))) :·: p₂ :·: p₁)) ∷ _) args = refl
    proof ((a :⇒ (p :·: p₃ :·: p₂ :·: p₁)) ∷ _) args = refl
{-# COMPILE AGDA2HS ruleOrSym #-}
