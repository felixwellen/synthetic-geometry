Quasi-compact schemes
=====================
This module defines quasi-compact (qc) schemes.
It is easier/possible to define open subsets of quasi compact spaces.
We will only admit (standard) finite covers, so this definition of qc-scheme could miss some qc-schemes.

```agda
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing

import SyntheticGeometry.SQC

module SyntheticGeometry.qc-Scheme
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.Open k
open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open import SyntheticGeometry.SQC k
open import SyntheticGeometry.Affine k k-local k-sqc


private variable ℓ' : Level

```

To define qc-schemes, we need the definition of open affine covers,
defined in [Open](Open.lagda.md).

```agda

is-qc-scheme : (X : Type ℓ') → hProp _
is-qc-scheme X =
  (∃[ n ∶ ℕ ] ∃[ U ∶ (Fin n → qc-opens-in X) ] is-affine-finite-qc-open-cover X U)

```

The projective space ℙ k n, defined [here](ProjectiveSpace.lagda.md) is a qc-scheme.
The affine qc-open cover U k n is defined in [this](ProjectiveSpace.lagda.md) module.

```agda

ℙ-is-qc-scheme : isLocal k → sqc-over-itself
  → (n : ℕ) → ⟨ is-qc-scheme (ℙ n) ⟩
ℙ-is-qc-scheme k-local k-sqc n =
  ∣ (n + 1) , ∣ (U n) , (covering n) , (λ i → U-is-affine n i) ∣₁ ∣₁

```
