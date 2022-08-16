Affine qc-schemes
=================

```agda
{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

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

import SyntheticGeometry.SQC

module SyntheticGeometry.Affine
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.Spec k
open import SyntheticGeometry.Open k
open SyntheticGeometry.SQC k

private variable ℓ' : Level

kₐ = initialCAlg k

```

An affine type is a type, that is equivalent to the spectrum of a fp algebra over the base ring k:

```agda


is-affine : Type ℓ' → hProp _
is-affine X =
  (∃[ A ∈ (CommAlgebra k ℓ) ] isFPAlgebra A × (X ≃ Spec A)) ,
  isPropPropTrunc

```

We want to see that: (Spec A ≃ Spec B) = (CommAlgebraIso A B)
which will need a couple of steps:

```agda

to-ev-hom : (X : Type ℓ') → X → Spec (pointwiseAlgebra X kₐ)
to-ev-hom X = evaluationHom X kₐ

to-ev-hom-on-Spec : (A : CommAlgebra k ℓ) → isFPAlgebra A → Spec A ≡ Spec (pointwiseAlgebra (Spec A) kₐ)
to-ev-hom-on-Spec A fp-A = cong Spec (sqc-path k-sqc A fp-A)

```

The following is used to define qc-schemes:

```agda

is-affine-finite-qc-open-cover : {n : ℕ}
  → (X : Type ℓ') → (U : Fin n → qc-opens-in X)
  → hProp _
is-affine-finite-qc-open-cover {n = n} X U =
  is-finite-qc-open-cover X U
  ⊓ (∀[ i ∶ Fin n ] is-affine (qc-open-as-type (U i)))

```

This was an attempt at an alternative definition of affine schemes, but it should be weaker.

```agda

is-coupled : Type ℓ' → hProp _
is-coupled X = (isEquiv (to-ev-hom X)) , isPropIsEquiv _

```
