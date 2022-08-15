Synthetic Quasicoherence
========================

Synthetic quasicoherence as defined in Ingo Blechschmidts thesis (Definition 18.18).
For now, we only consider the synthetic quasicoherence of the base ring k itself.

```agda
{-# OPTIONS --safe #-}
module SyntheticGeometry.SQC where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Function

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


open import SyntheticGeometry.Spec

```

The following defines synthetic quasicoherence for finitely presented algebras
over a given ring k. There are more general versions of synthetic quasicoherence
in Blechschmidt's thesis.

```agda

module _ {ℓ : Level} (k : CommRing ℓ) where
  private
    kₐ = initialCAlg k
    canonical-map : (A : CommAlgebra k ℓ) → ⟨ A ⟩ → (Spec k A → ⟨ k ⟩)
    canonical-map A a φ = φ $a a

  sqc-over-itself : Type _
  sqc-over-itself = (A : CommAlgebra k ℓ) → isFPAlgebra A → isEquiv (canonical-map A)

```

The canonical map is actually a homomorphism:

```agda
  module _ (A : CommAlgebra k ℓ) where
    open IsAlgebraHom
    open CommAlgebraStr {{...}}
    private instance
      _ = snd (pointwiseAlgebra (Spec k A) kₐ)
      _ = snd A

    canonical-hom : CommAlgebraHom A (pointwiseAlgebra (Spec k A) kₐ)
    fst canonical-hom = canonical-map A
    pres0 (snd canonical-hom) = funExt (λ ϕ → pres0 (snd ϕ))
    pres1 (snd canonical-hom) = funExt (λ ϕ → pres1 (snd ϕ))
    pres+ (snd canonical-hom) _ _ = funExt (λ ϕ → pres+ (snd ϕ) _ _)
    pres· (snd canonical-hom) _ _ = funExt (λ ϕ → pres· (snd ϕ) _ _)
    pres- (snd canonical-hom) _ = funExt (λ ϕ → pres- (snd ϕ) _)
    pres⋆ (snd canonical-hom) _ _ = funExt (λ ϕ → pres⋆ (snd ϕ) _ _)

```

Here are some properties of k that follow from its synthetic quasicoherence
together with its locality, as in Subsection 18.4.

```agda
module _ {ℓ : Level} (k : CommRing ℓ) (k-local : isLocal k) (k-sqc : sqc-over-itself k) where
  open CommRingStr (snd k)

  private
    kₐ = initialCAlg k

```

The ring k is a field in the sense that every non-zero element is invertible.
But even more, every nonzero vector contains an invertible element.

```agda
  generalized-field-property : {n : _} → (xs : FinVec _ n) → ¬(xs ≡ const 0r) → ∃[ i ∈ _ ] xs i ∈ k ˣ
  generalized-field-property xs xs≢0 =
    Consequences.onFGIdeals k k-local xs 1∈⟨xs⟩
    where
      ⟨xs⟩ : IdealsIn kₐ
      ⟨xs⟩ = generatedIdeal kₐ xs

      A : CommAlgebra k ℓ
      A = kₐ / ⟨xs⟩

      π : CommAlgebraHom kₐ A
      π = quotientHom kₐ ⟨xs⟩

      module A = CommAlgebraStr (snd A)
      module kₐ = CommAlgebraStr (snd kₐ)

      πx≡0 : (i : _) → π $a xs i ≡ A.0a
      πx≡0 i = isZeroFromIdeal (xs i) (incInIdeal kₐ xs i)

      finite-presentation-of-A : FinitePresentation A
      finite-presentation-of-A = Instances.R/⟨xs⟩FP k xs

      equiv : _ ≃ (Spec k A → _)
      equiv = _ , k-sqc A ∣ finite-presentation-of-A ∣₁

      Spec-A-empty : Spec k A → ⊥
      Spec-A-empty h = xs≢0 (funExt xs≡0)
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
            h $a (π $a xs i)  ≡⟨ cong (h $a_) (πx≡0 i) ⟩
            h $a A.0a         ≡⟨ IsAlgebraHom.pres0 (snd h) ⟩
            0r                ∎

      functions-on-Spec-A-trivial : {f g : Spec k A → _} → f ≡ g
      functions-on-Spec-A-trivial = funExt (λ p → Cubical.Data.Empty.rec (Spec-A-empty p))

      A-is-trivial : {a a' : _} → a ≡ a'
      A-is-trivial = isoFunInjective (equivToIso equiv) _ _ functions-on-Spec-A-trivial

      1∈⟨xs⟩ : kₐ.1a ∈ fst ⟨xs⟩
      1∈⟨xs⟩ = subst (λ J → kₐ.1a ∈ fst J) (kernel≡I kₐ ⟨xs⟩) A-is-trivial

  field-property : (x : _) → ¬(x ≡ 0r) → x ∈ k ˣ
  field-property x x≢0 =
    Prop.rec
      (snd ((k ˣ) x))
      (λ{ (zero , x∈kˣ) → x∈kˣ})
      (generalized-field-property (replicateFinVec 1 x) xs≢0)
    where
      xs≢0 : ¬ (replicateFinVec 1 x ≡ const 0r)
      xs≢0 xs≡0 = x≢0 (cong (λ f → f zero) xs≡0)

```
