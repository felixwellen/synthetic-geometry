Statement of Boundedness
========================


```agda
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra


module SyntheticGeometry.BoundednessStatement
  {ℓ : Level}
  (k : CommRing ℓ)
  where

open import SyntheticGeometry.Spec k

private
  variable
    ℓ' : Level

Boundedness : Type (ℓ-suc ℓ)
Boundedness =
  (A : CommAlgebra k ℓ) →
  isFPAlgebra A →
  (f : Spec A → ℕ) →
  ∃[ n ∈ ℕ ] ((x : Spec A) → f x ≤ n)
```
