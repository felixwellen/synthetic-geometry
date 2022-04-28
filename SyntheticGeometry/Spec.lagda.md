The Synthetic Spectrum
----------------------

All the mathematics presented here, is from [Ingo Blechschmidt](https://www.ingo-blechschmidt.eu/research.html)'s thesis or unpublished work of [David Jaz Myers](http://davidjaz.com/). The formalization in Agda is due to [Felix Cherubini](http://felix-cherubini.de) and Matthias Hutzler.

```
{-# OPTIONS --safe #-}
module SyntheticGeometry.Spec where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial

private
  variable
    ℓ ℓ' : Level

```

The synthetic spectrum of an k-algebra A, Spec A, is a notion that makes sense internally in the Zariski Topos. We assume a ring object k in the following, which we think of as (the functor of points of) the affine line 𝔸¹.

```

module _ (k : CommRing ℓ) where

  k-as-algebra = initialCAlg k

  Spec : CommAlgebra k ℓ' → Type _
  Spec A = CommAlgebraHom A k-as-algebra

```
