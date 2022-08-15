The Synthetic Spectrum
======================

All the mathematics presented here, is from [Ingo Blechschmidt](https://www.ingo-blechschmidt.eu/research.html)'s thesis or unpublished work of [David Jaz Myers](http://davidjaz.com/). The formalization in Agda is due to [Felix Cherubini](http://felix-cherubini.de) and Matthias Hutzler.

```agda
{-# OPTIONS --safe #-}
module SyntheticGeometry.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Fin hiding (Fin)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Pointwise
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra
import Cubical.Algebra.Algebra
open Cubical.Algebra.Algebra.AlgebraHoms

private
  variable
    ℓ ℓ' ℓ'' : Level

```

The synthetic spectrum of an k-algebra A, Spec A, is a notion that makes sense internally in the Zariski Topos.
We assume a ring object k in the following, which we think of as (the functor of points of) the affine line 𝔸¹.

```agda

module _ (k : CommRing ℓ) where

  k-as-algebra = initialCAlg k
  𝔸¹ = k-as-algebra

  Spec : CommAlgebra k ℓ' → Type _
  Spec A = CommAlgebraHom A k-as-algebra

  Spec→ : {A B : CommAlgebra k ℓ'} (f : CommAlgebraHom A B)
          → Spec B → Spec A
  Spec→ f α = α ∘a f

```

Standard n-dimensional affine space:

```agda

  std-affine-space : (n : ℕ) → Type _
  std-affine-space n = Spec (Polynomials n)

  𝔸 = std-affine-space

```

Since the type of polynomials we use is defined as a HIT,
which is a straight forward implementation of a free commutative algebra on a type D,
we can use the following abstract fact ...

```agda

  module _ (D : Type ℓ-zero) where
    k[D] = k [ D ]

    mapping-space-eq : Spec k[D] ≡ (D → ⟨ k ⟩)
    mapping-space-eq = homMapPath k-as-algebra

```

... to show that std-affine-space is a product:

```agda

  std-affine-space-as-product : (n : ℕ) → (𝔸 n) ≡ FinVec ⟨ k ⟩ n
  std-affine-space-as-product n = mapping-space-eq (Fin n)


  is-affine : Type ℓ' → hProp _
  is-affine X =
    (∃[ A ∈ (CommAlgebra k ℓ) ] isFPAlgebra A × (X ≃ Spec A)) ,
    isPropPropTrunc

  to-ev-hom : (X : Type ℓ') → X → Spec (pointwiseAlgebra X k-as-algebra)
  to-ev-hom X = evaluationHom X k-as-algebra

  is-affine' : Type ℓ' → hProp _
  is-affine' X = (isEquiv (to-ev-hom X)) , isPropIsEquiv _

```
