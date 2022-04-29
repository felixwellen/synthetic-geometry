Synthetic quasicoherence as defined in Ingo Blechschmidts thesis (Definition 18.18).
For now, we only consider the synthetic quasicoherence of the base ring k itself.

```agda
module SyntheticGeometry.SQC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.RingSolver.Reflection
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Data.Empty
open import Cubical.Data.FinData
open import Cubical.Relation.Nullary
import Cubical.Algebra.CommAlgebra.FreeCommAlgebra as FreeCommAlgebra

open import SyntheticGeometry.Spec


sqc-over-itself : {ℓ : Level} → CommRing ℓ → Set (ℓ-suc ℓ)
sqc-over-itself {ℓ} k = (A : CommAlgebra k ℓ) → isFPAlgebra A → isEquiv (canonical-map A)
  where
    canonical-map : (A : CommAlgebra k ℓ) → ⟨ A ⟩ → (Spec k A → ⟨ k ⟩)
    canonical-map A a φ = φ $a a

```
