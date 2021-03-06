The Synthetic Spectrum
----------------------

All the mathematics presented here, is from [Ingo Blechschmidt](https://www.ingo-blechschmidt.eu/research.html)'s thesis or unpublished work of [David Jaz Myers](http://davidjaz.com/). The formalization in Agda is due to [Felix Cherubini](http://felix-cherubini.de) and Matthias Hutzler.

```agda
{-# OPTIONS --safe #-}
module SyntheticGeometry.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Fin hiding (Fin)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra

private
  variable
    β β' : Level

```

The synthetic spectrum of an k-algebra A, Spec A, is a notion that makes sense internally in the Zariski Topos. We assume a ring object k in the following, which we think of as (the functor of points of) the affine line πΈΒΉ.

```agda

module _ (k : CommRing β) where

  k-as-algebra = initialCAlg k
  πΈΒΉ = k-as-algebra

  Spec : CommAlgebra k β' β Type _
  Spec A = CommAlgebraHom A k-as-algebra

  std-affine-space : (n : β) β Type _
  std-affine-space n = Spec (Polynomials n)

  πΈ = std-affine-space

  module _ (D : Type β-zero) where
    k[D] = k [ D ]

    mapping-space-eq : Spec k[D] β‘ (D β β¨ k β©)
    mapping-space-eq = homMapPath k-as-algebra

  std-affine-space-as-product : (n : β) β (πΈ n) β‘ FinVec (fst k-as-algebra) n
  std-affine-space-as-product n = mapping-space-eq (Fin n)

```
