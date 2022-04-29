The Synthetic Spectrum
----------------------

All the mathematics presented here, is from [Ingo Blechschmidt](https://www.ingo-blechschmidt.eu/research.html)'s thesis or unpublished work of [David Jaz Myers](http://davidjaz.com/). The formalization in Agda is due to [Felix Cherubini](http://felix-cherubini.de) and Matthias Hutzler.

```agda
{-# OPTIONS --safe #-}
module SyntheticGeometry.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Data.Empty

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial

private
  variable
    ℓ ℓ' : Level

```

The synthetic spectrum of an k-algebra A, Spec A, is a notion that makes sense internally in the Zariski Topos.
We assume a ring object k in the following, which we think of as (the functor of points of) the affine line 𝔸¹.

The synthetic spectrum of an k-algebra A, Spec A, is a notion that makes sense internally in the Zariski Topos. We assume a ring object k in the following, which we think of as (the functor of points of) the affine line 𝔸¹.

```agda

module _ (k : CommRing ℓ) where

  k-as-algebra = initialCAlg k

  Spec : CommAlgebra k ℓ' → Type _
  Spec A = CommAlgebraHom A k-as-algebra

```

The basic opens of the Zariski Topology are classically sets of primeideals D(f), such that p ∈ D(f) iff p ∌ f.
Synthetically, D(f) is the set of all α ∈ Spec A, such that f(α):≡α(f) is invertible:


```
  module _ (A : CommAlgebra k ℓ') where
    open CommAlgebraStr (snd k-as-algebra)

    D : (f : ⟨ A ⟩) → (Spec A → Type _)
    D f α = (fst α) f ∈ k ˣ

```
