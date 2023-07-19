A characterization of linear equivalence
========================================
We prove a slight reformulation of linear equivalence between non-zero vectors.

```agda
{-# OPTIONS --safe #-}

-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Foundations.HLevels using (isProp→)
open import Cubical.Foundations.Function using (case_of_)

import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing
open import Cubical.Algebra.Ring using (module RingTheory)
open import Cubical.Algebra.Module
open import Cubical.Algebra.Module.Instances.FinVec
open import Cubical.Algebra.AbGroup using (module AbGroupTheory)

open import Cubical.Relation.Nullary.Base using (¬_; yes; no)

import SyntheticGeometry.SQC

module SyntheticGeometry.ProjectiveSpace.CharacterizationOfLinearEquivalence
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open import SyntheticGeometry.SQC.Consequences k k-local k-sqc
```

```agda
module _
  {n : ℕ}
  ((a , a≠0) (b , b≠0) : 𝔸ⁿ⁺¹-0 n)
  where

  open LeftModuleStr (str (FinVecLeftModule (CommRing→Ring k) {n = n ℕ.+ 1}))
  open Units k

  char : (c : ⟨ k ⟩) → c ⋆ a ≡ b → linear-equivalent _ a b
  char c ca≡b = c , c-inv , ca≡b
    where
      c-inv : c ∈ k ˣ
      c-inv = PT.rec
        (str ((k ˣ) c))
        (λ (i , bi-inv) → fst (RˣMultDistributing c (a i) (subst (_∈ k ˣ) (sym (funExt⁻ ca≡b i)) bi-inv)))
        (generalized-field-property b b≠0)
```