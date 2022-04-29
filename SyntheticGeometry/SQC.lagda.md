Synthetic quasicoherence as defined in Ingo Blechschmidts thesis (Definition 18.18).
For now, we only consider the synthetic quasicoherence of the base ring k itself.

```
module SyntheticGeometry.SQC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Algebra
open import Cubical.Algebra.RingSolver.Reflection
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra
import Cubical.Algebra.CommAlgebra.FreeCommAlgebra as FreeCommAlgebra

open import Cubical.Data.Empty
open import Cubical.Data.FinData

open import Cubical.Relation.Nullary

open import SyntheticGeometry.Spec


sqc-over-itself : {ℓ : Level} → CommRing ℓ → Set (ℓ-suc ℓ)
sqc-over-itself {ℓ} k = (A : CommAlgebra k ℓ) → isFPAlgebra A → isEquiv (canonical-map A)
  where
    canonical-map : (A : CommAlgebra k ℓ) → ⟨ A ⟩ → (Spec k A → ⟨ k ⟩)
    canonical-map A a φ = φ $a a

```

Here are some properties of k that follow from its synthetic quasicoherence,
as in Subsection 18.4.

```
module _ {ℓ : Level} (k : CommRing ℓ) (k-sqc : sqc-over-itself k) where
  open CommRingStr (snd k)

  field-property : (x : ⟨ k ⟩) → ¬(x ≡ 0r) → x ∈ k ˣ
  field-property x x≢0 = {!!}
    where
      open FreeCommAlgebra.Construction using (const)
      A : CommAlgebra k ℓ
      A = FPAlgebra 0 (replicateFinVec 1 (const x))
      -- Would it be better to use "k / (x)" instead of this FPAlgebra "k[] / (x)"?
      finite-presentation-of-A : FinitePresentation A
      FinitePresentation.n finite-presentation-of-A = _
      FinitePresentation.m finite-presentation-of-A = _
      FinitePresentation.relations finite-presentation-of-A = _
      FinitePresentation.equiv finite-presentation-of-A = idCAlgEquiv A
      equiv : ⟨ A ⟩ ≃ (Spec k A → ⟨ k ⟩)
      equiv = _ , k-sqc A ∣ finite-presentation-of-A ∣
      module A = CommAlgebraStr (snd A)
      module kₐ = CommAlgebraStr (snd (initialCAlg k))
      x≡0-in-A : x A.⋆ A.1a ≡ A.0a
      x≡0-in-A = {!relationsHold!}
      Spec-A-empty : Spec k A → ⊥
      Spec-A-empty h = x≢0 x≡0
        where
          x≡0 : x ≡ 0r
          x≡0 = sym(
            0r
              ≡⟨ sym (IsAlgebraHom.pres0 (snd h)) ⟩
            (h $a A.0a)
              ≡⟨ cong (λ zero₁ → h $a zero₁) (sym x≡0-in-A) ⟩
            (h $a (x A.⋆ A.1a))
              ≡⟨ IsAlgebraHom.pres⋆ (snd h) x A.1a ⟩
            (x kₐ.⋆ (h $a A.1a))
              ≡⟨ cong (λ one → x kₐ.⋆ one) (IsAlgebraHom.pres1 (snd h)) ⟩
            (x kₐ.⋆ kₐ.1a)
              ≡⟨ refl ⟩
            (x · 1r)
              ≡⟨ step x ⟩
            x ∎)
            where
              step : (x : ⟨ k ⟩) → x · 1r ≡ x
              step = solve k
      functions-on-Spec-trivial : {f g : Spec k A → ⟨ k ⟩} → f ≡ g
      functions-on-Spec-trivial = funExt (λ p → Cubical.Data.Empty.rec (Spec-A-empty p))
      A-is-trivial : {a a' : ⟨ A ⟩} → a ≡ a'
      A-is-trivial = isoFunInjective (equivToIso equiv) _ _ functions-on-Spec-trivial
```
