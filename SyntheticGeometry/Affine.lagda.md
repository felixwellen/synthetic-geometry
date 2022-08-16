Affine qc-schemes
=================

```agda
{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

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

A coupled space is not neccessarily affine, but it is still the spectrum of an algebra,
which is coupled, i.e. the canonical map A → (Spec A → k) is an equivalence.
That the following definition is equivalent to this statement will be shown later,
we use another canonical map 'to-ev-hom' for the definition:

```agda

to-ev-hom : (X : Type ℓ') → X → Spec (pointwiseAlgebra X kₐ)
to-ev-hom X = evaluationHom X kₐ

is-coupled : Type ℓ' → hProp _
is-coupled X = (isEquiv (to-ev-hom X)) , isPropIsEquiv _

```

We want to see that: (Spec A ≃ Spec B) = (CommAlgebraIso A B) for any fp algebras A and B.
We will show the more general statement for coupled algebras, which will need a couple of steps:

First, there is a canonical morphism from any type to a spectrum,
which has a left inverse, when the type is a spectrum.


```agda

left-inv-to-ev-hom : (A : CommAlgebra k ℓ') → Spec (pointwiseAlgebra (Spec A) kₐ) → Spec A
left-inv-to-ev-hom A = Spec→ {A = A} {B = pointwiseAlgebra (Spec A) kₐ} (canonical-hom A)

is-left-inv-to-ev-hom : (A : CommAlgebra k ℓ') → (left-inv-to-ev-hom A) ∘ to-ev-hom (Spec A) ≡ idfun (Spec A)
is-left-inv-to-ev-hom A i α = typed-eq i
  where typed-eq : Spec→ {A = A} {B = pointwiseAlgebra (Spec A) kₐ} (canonical-hom A) (to-ev-hom (Spec A) α) ≡ α
        typed-eq = make-Spec-eq {A = A} refl

```


```agda

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