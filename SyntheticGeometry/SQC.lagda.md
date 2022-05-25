Synthetic quasicoherence as defined in Ingo Blechschmidts thesis (Definition 18.18).
For now, we only consider the synthetic quasicoherence of the base ring k itself.

```agda
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
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.FGIdeal
open import Cubical.Algebra.CommRingSolver.Reflection
import Cubical.Algebra.CommAlgebra.FreeCommAlgebra as FreeCommAlgebra

open import Cubical.Data.Empty
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation as Prop

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

```agda
module _ {ℓ : Level} (k : CommRing ℓ) (k-sqc : sqc-over-itself k) where
  open CommRingStr (snd k)

  kₐ = k-as-algebra k

  field-property : (x : ⟨ k ⟩) → ¬(x ≡ 0r) → x ∈ k ˣ
  field-property x x≢0 =
    Prop.rec
      (snd ((k ˣ) x))
      (λ {(α , isLC)
        → α Fin.zero ,
          (x · α zero          ≡⟨ useSolver x (α zero) ⟩
           (α zero · x + 0r)   ≡⟨ sym isLC ⟩
           1r ∎)
       })
      1∈⟨x⟩
    where
      useSolver : (x α : ⟨ k ⟩) → x · α ≡ α · x + 0r
      useSolver = solve k

      open FreeCommAlgebra.Construction using (const)

      ⟨x⟩ : IdealsIn kₐ
      ⟨x⟩ = generatedIdeal kₐ (replicateFinVec 1 x)

      A : CommAlgebra k ℓ
      A = kₐ / ⟨x⟩

      π : CommAlgebraHom kₐ A
      π = quotientHom kₐ ⟨x⟩

      module A = CommAlgebraStr (snd A)
      module kₐ = CommAlgebraStr (snd kₐ)

      πx≡0 : π $a x ≡ A.0a
      πx≡0 = isZeroFromIdeal {A = kₐ} {I = ⟨x⟩} x
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
                evPoly A (relation zero) (λ ())    ≡⟨ sym (evPolyHomomorphic kₐ A π (const x) vals') ⟩
                π $a (evPoly kₐ (const x) vals')   ≡⟨ cong (π $a_) (·Rid x) ⟩
                π $a x                             ≡⟨ πx≡0 ⟩
                A.0a                               ∎

          fromA : CommAlgebraHom A B
          fromA = quotientInducedHom kₐ ⟨x⟩ B (initialMap k B) {!!}

      equiv : ⟨ A ⟩ ≃ (Spec k A → ⟨ k ⟩)
      equiv = _ , k-sqc A ∥_∥₁.∣ finite-presentation-of-A ∣₁

      Spec-A-empty : Spec k A → ⊥
      Spec-A-empty h = x≢0 x≡0
        where
          open AlgebraHoms using (compAlgebraHom)
          -- We use _∘a_ (compAlgebraHom) for composition because the implicit arguments
          -- of CommAlgebraHoms._∘ca_ can not be inferred. (And even using
          -- CommAlgebraHoms.compCommAlgebraHom with explicit arguments makes type checking
          -- hang indefinitely.)
          id≡h∘π : idCAlgHom kₐ ≡ h ∘a π
          id≡h∘π = initialMapProp k kₐ (idCAlgHom kₐ) (h ∘a π)
          x≡0 : x ≡ 0r
          x≡0 =
            x              ≡⟨ cong (_$a x) id≡h∘π ⟩
            h $a (π $a x)  ≡⟨ cong (h $a_) πx≡0 ⟩
            h $a A.0a      ≡⟨ IsAlgebraHom.pres0 (snd h) ⟩
            0r             ∎

      functions-on-Spec-A-trivial : {f g : Spec k A → ⟨ k ⟩} → f ≡ g
      functions-on-Spec-A-trivial = funExt (λ p → Cubical.Data.Empty.rec (Spec-A-empty p))

      A-is-trivial : {a a' : ⟨ A ⟩} → a ≡ a'
      A-is-trivial = isoFunInjective (equivToIso equiv) _ _ functions-on-Spec-A-trivial

      1∈kernel-π : kₐ.1a ∈ fst (kernel kₐ A π)
      1∈kernel-π = A-is-trivial

      1∈⟨x⟩ : kₐ.1a ∈ fst ⟨x⟩
      1∈⟨x⟩ = subst (λ J → kₐ.1a ∈ fst J) (kernel≡I kₐ ⟨x⟩) 1∈kernel-π
```
