Affine qc-schemes
=================

```agda
{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Logic

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Pointwise
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommRing.LocalRing
import Cubical.Algebra.Algebra
open Cubical.Algebra.Algebra.AlgebraHoms

open import SyntheticGeometry.Spec
open import SyntheticGeometry.SQC
open import SyntheticGeometry.Open

module SyntheticGeometry.Affine {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : sqc-over-itself k)
  where

private variable ℓ' : Level

kₐ = initialCAlg k

```

An affine type is a type, that is equivalent to a fp algebra over the base ring k:

```agda


is-affine : Type ℓ' → hProp _
is-affine X =
  (∃[ A ∈ (CommAlgebra k ℓ) ] isFPAlgebra A × (X ≃ Spec k A)) ,
  isPropPropTrunc

to-ev-hom : (X : Type ℓ') → X → Spec k (pointwiseAlgebra X kₐ)
to-ev-hom X = evaluationHom X kₐ

is-affine' : Type ℓ' → hProp _
is-affine' X = (isEquiv (to-ev-hom X)) , isPropIsEquiv _

is-affine-finite-qc-open-cover : {n : ℕ}
  → (X : Type ℓ') → (U : Fin n → qc-opens-in k X)
  → hProp _
is-affine-finite-qc-open-cover {n = n} X U =
  is-finite-qc-open-cover k X U
  ⊓ (∀[ i ∶ Fin n ] is-affine (qc-open-as-type k (U i)))

```
