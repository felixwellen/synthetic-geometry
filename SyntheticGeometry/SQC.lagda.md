Synthetic quasicoherence as defined in Ingo Blechschmidts thesis (Definition 18.18).
For now, we only consider the synthetic quasicoherence of the base ring k itself.

```agda
module SyntheticGeometry.SQC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function

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

open import Cubical.Data.Sigma
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

  kₐ = initialCAlg k

```

The ring k is a field in the sense that every non-zero element is invertible.
But even more, an invertible elements exists in every nonzero vector.

```agda
  generalized-field-property : {n : _} → (xs : FinVec ⟨ k ⟩ n) → ¬(xs ≡ const 0r) → ∃[ i ∈ _ ] xs i ∈ k ˣ
  generalized-field-property xs xs≢0 =
    {!
    Prop.rec
      (snd ((k ˣ) x))
      (λ {(α , isLC)
        → α Fin.zero ,
          (x · α zero          ≡⟨ useSolver x (α zero) ⟩
           (α zero · x + 0r)   ≡⟨ sym isLC ⟩
           1r ∎)
       })
      1∈⟨x⟩ !}
    where
      useSolver : (x α : ⟨ k ⟩) → x · α ≡ α · x + 0r
      useSolver = solve k

      open FreeCommAlgebra.Construction using (const)

      ⟨xs⟩ : IdealsIn kₐ
      ⟨xs⟩ = generatedIdeal kₐ xs

      A : CommAlgebra k ℓ
      A = kₐ / ⟨xs⟩

      π : CommAlgebraHom kₐ A
      π = quotientHom kₐ ⟨xs⟩


      module A = CommAlgebraStr (snd A)
      module kₐ = CommAlgebraStr (snd kₐ)

      πx≡0 : (i : _) → π $a xs i ≡ A.0a
      πx≡0 i = isZeroFromIdeal {A = kₐ} {I = ⟨xs⟩} (xs i)
               (incInIdeal kₐ xs i)

      finite-presentation-of-A : FinitePresentation A
      finite-presentation-of-A = Instances.R/⟨xs⟩FP k xs
{-

      equiv : ⟨ A ⟩ ≃ (Spec k A → ⟨ k ⟩)
      equiv = _ , k-sqc _ ∥_∥₁.∣ finite-presentation-of-A ∣₁

      Spec-A-empty : Spec k A → ⊥
      Spec-A-empty h = xs≢0 xs≡0 -- TODO
        where
          open AlgebraHoms using (compAlgebraHom)
          -- We use _∘a_ (compAlgebraHom) for composition because the implicit arguments
          -- of CommAlgebraHoms._∘ca_ can not be inferred. (And even using
          -- CommAlgebraHoms.compCommAlgebraHom with explicit arguments makes type checking
          -- hang indefinitely.)
          id≡h∘π : idCAlgHom kₐ ≡ h ∘a π
          id≡h∘π = initialMapProp k kₐ (idCAlgHom kₐ) (h ∘a π)
          xs≡0 : (i : _) → xs i ≡ 0r
          xs≡0 i =
            xs i              ≡⟨ cong (_$a xs i) id≡h∘π ⟩
            h $a (π $a xs i)  ≡⟨ cong (h $a_) πx≡0 ⟩
            h $a A.0a         ≡⟨ IsAlgebraHom.pres0 (snd h) ⟩
            0r                ∎

      functions-on-Spec-A-trivial : {f g : Spec k A → ⟨ k ⟩} → f ≡ g
      functions-on-Spec-A-trivial = funExt (λ p → Cubical.Data.Empty.rec (Spec-A-empty p))

      A-is-trivial : {a a' : ⟨ A ⟩} → a ≡ a'
      A-is-trivial = isoFunInjective (equivToIso equiv) _ _ functions-on-Spec-A-trivial

      1∈kernel-π : kₐ.1a ∈ fst (kernel kₐ A π)
      1∈kernel-π = A-is-trivial

      1∈⟨xs⟩ : kₐ.1a ∈ fst ⟨xs⟩
      1∈⟨xs⟩ = subst (λ J → kₐ.1a ∈ fst J) (kernel≡I kₐ ⟨xs⟩) 1∈kernel-π
-}
```
