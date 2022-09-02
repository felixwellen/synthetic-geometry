Synthetic Quasicoherence
========================

Synthetic quasicoherence as defined in Ingo Blechschmidts thesis (Definition 18.18).
For now, we only consider the synthetic quasicoherence of the base ring k itself.

```agda
{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Pointwise
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra renaming (inducedHom to quotientInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.FGIdeal
import Cubical.Algebra.CommAlgebra.FreeCommAlgebra as FreeCommAlgebra

open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.FinData

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver.Reflection

module SyntheticGeometry.SQC
  {ℓ : Level}
  (k : CommRing ℓ)
  where

open import SyntheticGeometry.Spec k
private variable ℓ' : Level
```

The following defines synthetic quasicoherence for finitely presented algebras
over a given ring k. There are more general versions of synthetic quasicoherence
in Blechschmidt's thesis.

```agda

private
  kₐ = initialCAlg k

to-ev-map : (A : CommAlgebra k ℓ') → ⟨ A ⟩ → (Spec A → ⟨ k ⟩)
to-ev-map A a φ = φ $a a

sqc-over-itself : Type _
sqc-over-itself = (A : CommAlgebra k ℓ) → isFPAlgebra A → isEquiv (to-ev-map A)

is-coupled-algebra : (A : CommAlgebra k ℓ') → hProp _
is-coupled-algebra A = isEquiv (to-ev-map A) , isPropIsEquiv _

```

The canonical map is actually a homomorphism:

```agda
module _ (A : CommAlgebra k ℓ') where
  open IsAlgebraHom
  open CommAlgebraStr {{...}}
  private instance
    _ = snd (pointwiseAlgebra (Spec A) kₐ)
    _ = snd A

  canonical-hom : CommAlgebraHom A (pointwiseAlgebra (Spec A) kₐ)
  fst canonical-hom = to-ev-map A
  pres0 (snd canonical-hom) = funExt (λ ϕ → pres0 (snd ϕ))
  pres1 (snd canonical-hom) = funExt (λ ϕ → pres1 (snd ϕ))
  pres+ (snd canonical-hom) _ _ = funExt (λ ϕ → pres+ (snd ϕ) _ _)
  pres· (snd canonical-hom) _ _ = funExt (λ ϕ → pres· (snd ϕ) _ _)
  pres- (snd canonical-hom) _ = funExt (λ ϕ → pres- (snd ϕ) _)
  pres⋆ (snd canonical-hom) _ _ = funExt (λ ϕ → pres⋆ (snd ϕ) _ _)

```
