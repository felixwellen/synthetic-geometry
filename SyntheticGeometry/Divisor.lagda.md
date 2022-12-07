Divisors
========

Start of conjectural definition of divisors
```agda
{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

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


module SyntheticGeometry.Divisor
  {ℓ : Level}
  (k : CommRing ℓ)
  where

private variable
  ℓ' : Level
```
An element x ∈ A is called regular, if the multiplication with x is injective.

```agda
module _ (A : CommAlgebra k ℓ') where
  open CommAlgebraStr (snd A)
  _is-regular : ⟨ A ⟩ → Type _
  x is-regular = (a : ⟨ A ⟩) → x · a ≡ 0a  → a ≡ 0a

  Reg : Type _
  Reg = Σ[ x ∈ ⟨ A ⟩ ] x is-regular

```

Divisors on Spec A are regular elements of A up to multiplication by a unit of A.
This is the same as identifying regular elements that generate the same principal ideal.

```agda

private module ConstructDivisors (A : CommAlgebra k ℓ') where
  open CommAlgebraStr (snd A)
  asRing = CommAlgebra→CommRing A
  _≈_ : Reg A → Reg A → Type _
  (x , x-reg) ≈ (y , y-reg) = ∃[ u ∈ ⟨ A ⟩ ] (u ∈ asRing ˣ) × (x · u ≡ y)

AffDiv : (A : CommAlgebra k ℓ') → Type _
AffDiv A = Reg A / ConstructDivisors._≈_ A

```

