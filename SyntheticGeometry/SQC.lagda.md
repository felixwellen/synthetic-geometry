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

      finite-presentation-of-A : FinitePresentation A
      finite-presentation-of-A = {!!}

      equiv : ⟨ A ⟩ ≃ (Spec k A → ⟨ k ⟩)
      equiv = _ , k-sqc A ∣ finite-presentation-of-A ∣

      q : CommAlgebraHom kₐ A
      q = quotientMap kₐ ideal

      module A = CommAlgebraStr (snd A)
--      module kₐ = CommAlgebraStr (snd (initialCAlg k))

      qx≡0 : q $a x ≡ A.0a
      qx≡0 = isZeroFromIdeal {A = kₐ} {I = ideal} x
               (incInIdeal kₐ (replicateFinVec 1 x) zero)

{-
      x≡0-in-A : x A.⋆ A.1a ≡ A.0a
      x≡0-in-A =
        x A.⋆ A.1a           ≡⟨ cong (λ one → x A.⋆ one) pres1 ⟩
        x A.⋆ (q $a kₐ.1a)   ≡⟨ pres⋆ x _ ⟩
        q $a (x kₐ.⋆ kₐ.1a)  ≡⟨ cong (λ x' → q $a x') (kₐ.·Rid _) ⟩
        q $a x               ≡⟨ qx≡0 ⟩
        A.0a                 ∎
        where
          open IsAlgebraHom (snd q)
-}

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
{-
          sym (
            0r                    ≡⟨ sym pres0 ⟩
            (h $a A.0a)           ≡⟨ cong (λ z → h $a z) (sym {! x≡0-in-A !}) ⟩
            (h $a (x A.⋆ A.1a))   ≡⟨ pres⋆ x A.1a ⟩
            (x kₐ.⋆ (h $a A.1a))  ≡⟨ cong (λ one → x kₐ.⋆ one) pres1 ⟩
            (x kₐ.⋆ kₐ.1a)        ≡⟨ kₐ.·Rid _ ⟩
            x                     ∎ )
-}

      functions-on-Spec-A-trivial : {f g : Spec k A → ⟨ k ⟩} → f ≡ g
      functions-on-Spec-A-trivial = funExt (λ p → Cubical.Data.Empty.rec (Spec-A-empty p))

      A-is-trivial : {a a' : ⟨ A ⟩} → a ≡ a'
      A-is-trivial = isoFunInjective (equivToIso equiv) _ _ functions-on-Spec-A-trivial
```
