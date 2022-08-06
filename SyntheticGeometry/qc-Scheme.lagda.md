Quasi-compact schemes
=====================
This module defines quasi-compact (qc) schemes.
It is easier/possible to define open subsets of quasi compact spaces.
We will only admit (standard) finite covers, so this definition of qc-scheme could miss some qc-schemes.

```agda
module SyntheticGeometry.qc-Scheme where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing

open import SyntheticGeometry.Open
open import SyntheticGeometry.Spec

private variable ℓ ℓ' : Level

```

To define qc-schemes, we need the definition of open affine covers,
defined in [Open](Open.lagda.md).

```agda

module _ (k : CommRing ℓ) where
  is-qc-scheme : (X : Type ℓ') → hProp _
  is-qc-scheme X =
    (∃[ n ∈ ℕ ] ∃[ U ∈ (Fin n → qc-opens-in k X) ] fst (is-affine-finite-qc-open-cover k X U)) ,
    isPropPropTrunc

```
