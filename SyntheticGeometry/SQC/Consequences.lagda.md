Consequences of Synthetic Quasicoherence
========================================

In this file we show some first consequences of the synthetic quasicoherence
of our base ring k.
We also freely assume (here and in many other places) that k is a local ring.
After all, we imagine k to be the structure sheaf of the big Zariski topos,
which is the universal local ring.

In particular we derive field like properties of k.
This is taken from Subsection 18.4 of Ingo Blechschmidt's thesis.

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
open import Cubical.Algebra.CommAlgebra.FPAlgebra.Instances using (R/⟨xs⟩FP)
open import Cubical.Algebra.CommAlgebra.QuotientAlgebra renaming (inducedHom to quotientInducedHom)
open import Cubical.Algebra.CommAlgebra.Ideal
open import Cubical.Algebra.CommAlgebra.Kernel
open import Cubical.Algebra.CommAlgebra.FGIdeal

open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.FinData

open import Cubical.HITs.PropositionalTruncation as Prop

open import Cubical.Relation.Nullary

open import Cubical.Tactics.CommRingSolver.Reflection

import SyntheticGeometry.SQC

module SyntheticGeometry.SQC.Consequences
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.Spec k
open SyntheticGeometry.SQC k

private variable ℓ' : Level
```


The equivalence in sqc is actually an algebra isomorphism and therefore also
a path between the algebras:

```agda

private
  kₐ = initialCAlg k

module _ (k-sqc : sqc-over-itself) (A : CommAlgebra k ℓ) (fp-A : isFPAlgebra A) where
  sqc-alg-equiv : CommAlgebraEquiv A (pointwiseAlgebra (Spec A) kₐ)
  fst sqc-alg-equiv = to-ev-map A , k-sqc A fp-A
  snd sqc-alg-equiv = snd (canonical-hom A)

  sqc-path : A ≡ pointwiseAlgebra (Spec A) kₐ
  sqc-path = fst (CommAlgebraPath k A (pointwiseAlgebra (Spec A) kₐ)) sqc-alg-equiv

```

The ring k is a field in the sense that every non-zero element is invertible.
But even more, every nonzero vector contains an invertible element.

```agda
open CommRingStr (snd k)

generalized-field-property : {n : _} → (xs : FinVec ⟨ k ⟩ n) → ¬(xs ≡ const 0r) → ∃[ i ∈ _ ] xs i ∈ k ˣ
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
    finite-presentation-of-A = R/⟨xs⟩FP k xs

    equiv : ⟨ A ⟩ ≃ (Spec A → ⟨ k ⟩)
    equiv = _ , k-sqc A ∣ finite-presentation-of-A ∣₁

    Spec-A-empty : Spec A → ⊥
    Spec-A-empty h = xs≢0 (funExt xs≡0)
      where
        open AlgebraHoms using (_∘a_)
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

    functions-on-Spec-A-trivial : {f g : Spec A → ⟨ k ⟩} → f ≡ g
    functions-on-Spec-A-trivial = funExt (λ p → Cubical.Data.Empty.rec (Spec-A-empty p))

    A-is-trivial : {a a' : ⟨ A ⟩} → a ≡ a'
    A-is-trivial = isoFunInjective (equivToIso equiv) _ _ functions-on-Spec-A-trivial

    1∈⟨xs⟩ : kₐ.1a ∈ fst ⟨xs⟩
    1∈⟨xs⟩ = subst (λ J → kₐ.1a ∈ fst J) (kernel≡I kₐ ⟨xs⟩) A-is-trivial

field-property : (x : ⟨ k ⟩) → ¬(x ≡ 0r) → x ∈ k ˣ
field-property x x≢0 =
  Prop.rec
    (snd ((k ˣ) x))
    (λ{ (zero , x∈kˣ) → x∈kˣ})
    (generalized-field-property (replicateFinVec 1 x) xs≢0)
  where
    xs≢0 : ¬ (replicateFinVec 1 x ≡ const 0r)
    xs≢0 xs≡0 = x≢0 (cong (λ f → f zero) xs≡0)

```

