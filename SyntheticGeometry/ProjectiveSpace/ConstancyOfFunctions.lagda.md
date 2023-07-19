Constancy of functions ℙⁿ → k
=============================
We show that all functions ℙⁿ → k are constant,
assuming that all functions ℙ¹ → k are constant
(which we did not formalize yet).

```agda
{-# OPTIONS --safe #-}

-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Foundations.HLevels using (isProp→)
open import Cubical.Foundations.Function -- using (case_of_)

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

module SyntheticGeometry.ProjectiveSpace.ConstancyOfFunctions
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open import SyntheticGeometry.SQC.Consequences k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace.StandardPoints k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace.P0 k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace.LineThroughPoints k k-local k-sqc
```

We always have a base point p₀ available.

```agda
private
  p₀ : (n : ℕ) → ℙ n
  p₀ n = p (subst Fin (ℕ.+-comm 1 n) zero)
    where
    open StandardPoints
```

The case n = 0 is simple.

```agda
module n=0-Case
  where

  all-functions-constant :
    (f : ℙ 0 → ⟨ k ⟩) →
--    f ≡ const (f (p₀ 0))
    2-Constant f
  all-functions-constant f p q = cong f (isContr→isProp isContr-ℙ⁰ p q)
--  all-functions-constant f = funExt (λ p → cong f (isContr→isProp isContr-ℙ⁰ _ _))
```

Let us now deduce the case n ≥ 1 from the case n = 1.

```agda
equal-on-distinct-points :
  ((f : ℙ 1 → ⟨ k ⟩) → 2-Constant f) →
  {n : ℕ} →
  (f : ℙ n → ⟨ k ⟩) →
  (p q : ℙ n) →
  ¬ (p ≡ q) →
  f p ≡ f q
equal-on-distinct-points ℙ¹-case f p q p≢q =
  PT.rec
    (is-set _ _)
    (λ (g , hits-p , hits-q) →
      f p                ≡⟨ sym (cong f hits-p) ⟩
      f (g (ℙ¹.p zero))  ≡⟨ ℙ¹-case (f ∘ g) _ _ ⟩
      f (g (ℙ¹.p one))   ≡⟨ cong f hits-q ⟩
      f q                ∎)
    (line-through-points-exists p q p≢q)
  where
  open CommRingStr (str k) using (is-set)
  module ℙ¹ = StandardPoints {n = 1}

module n≥1-Case
  (n-1 : ℕ)
  where

  n = ℕ.suc n-1

  open StandardPoints {n = n}
  p₁ = p (subst Fin (ℕ.+-comm 1 n) one)

  all-functions-constant :
    (f : ℙ n → ⟨ k ⟩) →
--    f ≡ const (f (p₀ n))
    2-Constant f
  all-functions-constant f = {!!}
```

```agda
all-functions-constant :
  {n : ℕ} →
  ((f : ℙ one → ⟨ k ⟩) → 2-Constant f) →
  (f : ℙ n → ⟨ k ⟩) →
--  f ≡ const (f (p₀ n))
  2-Constant f
all-functions-constant ℙ¹-case f = {!!}
```
