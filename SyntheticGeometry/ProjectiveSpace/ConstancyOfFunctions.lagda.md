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
open import SyntheticGeometry.ProjectiveSpace.LineThroughPoints k k-local k-sqc
```

```agda
allFunctionsConstant :
  {n : ℕ} →
  ((f : ℙ one → ⟨ k ⟩) → 2-Constant f) →
  (f : ℙ n → ⟨ k ⟩) →
  2-Constant f
allFunctionsConstant ℙ¹-case f p q = {!!}
```
