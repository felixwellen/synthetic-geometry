Standard points of projective space
===================================

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

module SyntheticGeometry.ProjectiveSpace.StandardPoints
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open import SyntheticGeometry.SQC.Consequences k k-local k-sqc
```

Here are certain "standard" points of projective space.

```agda
-- TODO: export this somewhere
private
  [_] : {n : ℕ} → 𝔸ⁿ⁺¹-0 n → ℙ n
  [_] = SQ.[_]

module StandardPoints
  {n : ℕ}
  where

  open CommRingStr (snd k)

  -- TODO: define standard basis vectors in the cubical libraries and use those instead
  standard-basis-vector : Fin (n ℕ.+ 1) → FinVec ⟨ k ⟩ (n ℕ.+ 1)
  standard-basis-vector i j =
    case (discreteFin i j) of
      λ{ (yes _) → 1r
       ; (no _) → 0r
       }

  standard-basis-vector-1-entry : (i : _) → standard-basis-vector i i ≡ 1r
  standard-basis-vector-1-entry i with (discreteFin i i)
  ... | yes _ = refl
  ... | no i≠i = ⊥.rec (i≠i refl)

  p : Fin (n ℕ.+ 1) → ℙ n
  p i =
    [ standard-basis-vector i ,
      (λ ≡0 → 1≢0 (
        1r                         ≡⟨ sym (standard-basis-vector-1-entry i) ⟩
        standard-basis-vector i i  ≡⟨ funExt⁻ ≡0 i ⟩
        0r                         ∎ )) ]
    where
    open Consequences k k-local
```

