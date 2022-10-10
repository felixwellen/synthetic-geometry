The Synthetic Spectrum
======================

All the mathematics presented in this file and on SQC [here](SQC/Consequences.lagda.md) and [here](SQC.lagda.md), is from [Ingo Blechschmidt](https://www.ingo-blechschmidt.eu/research.html)'s thesis, where the idea how to translate to homotopy type theory is unpublished work of [David Jaz Myers](http://davidjaz.com/). The formalization in Agda is due to the authors, [Felix Cherubini](http://felix-cherubini.de) and Matthias Hutzler. Ingo Blechschmidt also suggested to us to use the definition of [qc-opens](Open.lagda.md). This work was greatly supported by discussions with Thierry Coquand.

```agda
{-# OPTIONS --safe #-}

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
open Cubical.Algebra.Algebra.AlgebraEquivs
open Cubical.Algebra.Algebra using (AlgebraHom≡)


module SyntheticGeometry.Spec
  {ℓ : Level}
  (k : CommRing ℓ)
  where

private
  variable
    ℓ' ℓ'' : Level
    A B : CommAlgebra k ℓ'

```

The synthetic spectrum of an k-algebra A, Spec A, is a notion that makes sense internally in the Zariski Topos.
We assume a ring object k in the following, which we think of as (the functor of points of) the affine line 𝔸¹.

```agda

k-as-algebra = initialCAlg k
𝔸¹ = k-as-algebra

Spec : CommAlgebra k ℓ' → Type _
Spec A = CommAlgebraHom A k-as-algebra

make-Spec-eq : {x y : Spec A} → fst x ≡ fst y → x ≡ y
make-Spec-eq = AlgebraHom≡

module _ {A : CommAlgebra k ℓ'} {B : CommAlgebra k ℓ''} where
  Spec→ :  (f : CommAlgebraHom A B)
          → Spec B → Spec A
  Spec→ f α = compAlgebraHom f α

  Spec→≃ : (f : CommAlgebraEquiv A B)
          → Spec B ≃ Spec A
  fst (Spec→≃ f) = Spec→ (fst (fst f) , snd f)
  snd (Spec→≃ f) = snd (preCompAlgEquiv f)
```

Standard n-dimensional affine space
-----------------------------------

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

```
