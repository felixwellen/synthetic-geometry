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
open import Cubical.Algebra.CommRingSolver.Reflection
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra renaming (inducedHom to quotientInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.FGIdeal
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

  kₐ = k-as-algebra k

  field-property : (x : ⟨ k ⟩) → ¬(x ≡ 0r) → x ∈ k ˣ
  field-property x x≢0 = {!!}
    where
      open FreeCommAlgebra.Construction using (const)

      ideal : IdealsIn kₐ
      ideal = generatedIdeal kₐ (replicateFinVec 1 x)

      A : CommAlgebra k ℓ
      A = kₐ / ideal

      q : CommAlgebraHom kₐ A
      q = quotientMap kₐ ideal

      module A = CommAlgebraStr (snd A)
      module kₐ = CommAlgebraStr (snd kₐ)

      qx≡0 : q $a x ≡ A.0a
      qx≡0 = isZeroFromIdeal {A = kₐ} {I = ideal} x
               (incInIdeal kₐ (replicateFinVec 1 x) zero)

      finite-presentation-of-A : FinitePresentation A
      FinitePresentation.n finite-presentation-of-A = 0
      FinitePresentation.m finite-presentation-of-A = 1
      FinitePresentation.relations finite-presentation-of-A = replicateFinVec 1 (const x)
      FinitePresentation.equiv finite-presentation-of-A = {!!}
        where
          B = FPAlgebra 0 (replicateFinVec 1 (const x))

          toA : CommAlgebraHom B A
          toA = inducedHom 0 relation A (λ ()) relation-holds
            where
              vals : FinVec ⟨ A ⟩ 0
              vals ()
              vals' : FinVec ⟨ kₐ ⟩ 0
              vals' ()
              relation = replicateFinVec 1 (const x)
              relation-holds = λ zero →
                evPoly A (relation zero) (λ ())    ≡⟨ sym (evPolyHomomorphic kₐ A q (const x) vals') ⟩
                q $a (evPoly kₐ (const x) vals')   ≡⟨ cong (λ x' → q $a x') (·Rid x) ⟩
                q $a x                             ≡⟨ qx≡0 ⟩
                A.0a                               ∎

          fromA : CommAlgebraHom A B
          fromA = quotientInducedHom kₐ ideal B (initialMap k B) {!inclOfFGIdeal!}

      equiv : ⟨ A ⟩ ≃ (Spec k A → ⟨ k ⟩)
      equiv = _ , k-sqc A ∣ finite-presentation-of-A ∣

      Spec-A-empty : Spec k A → ⊥
      Spec-A-empty h = x≢0 x≡0
        where
          open CommAlgebraHoms
          id≡q∘h = initialMapProp k kₐ (idCAlgHom kₐ) (compCommAlgebraHom kₐ A kₐ q h)
          x≡0 : x ≡ 0r
          x≡0 =
            x              ≡⟨ cong (λ f → f $a x) id≡q∘h ⟩
            h $a (q $a x)  ≡⟨ cong (λ y → h $a y) qx≡0 ⟩
            h $a A.0a      ≡⟨ IsAlgebraHom.pres0 (snd h) ⟩
            0r             ∎

      functions-on-Spec-A-trivial : {f g : Spec k A → ⟨ k ⟩} → f ≡ g
      functions-on-Spec-A-trivial = funExt (λ p → Cubical.Data.Empty.rec (Spec-A-empty p))

      A-is-trivial : {a a' : ⟨ A ⟩} → a ≡ a'
      A-is-trivial = isoFunInjective (equivToIso equiv) _ _ functions-on-Spec-A-trivial
```
