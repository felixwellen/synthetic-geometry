Statement of Boundedness
========================


```agda
-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

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
