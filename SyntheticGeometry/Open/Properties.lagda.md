Properties of (qc-)open propositions and subsets
================================================

```agda
{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels using (hProp; isProp→)
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Foundations.Function using (_∘_; const)

open import Cubical.Functions.Logic using (⇒∶_⇐∶_; isProp⟨⟩)

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Data.FinData using (FinVec; ¬Fin0)
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing using (isLocal)

open import Cubical.Relation.Nullary
  using (¬_; isProp¬)
  renaming (Stable to ¬¬Stable; Stable¬ to ¬¬Stable¬)

import SyntheticGeometry.SQC

module SyntheticGeometry.Open.Properties
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.Spec k
open import SyntheticGeometry.Open k
open import SyntheticGeometry.Affine k k-local k-sqc
open SyntheticGeometry.SQC k

```

qc-open propositions are double negation stable.

```agda

stable-std-qc-open-prop : {n : ℕ} → (x : FinVec ⟨ k ⟩ n) → ¬¬Stable ⟨ std-qc-open-prop x ⟩
stable-std-qc-open-prop x = subst ¬¬Stable (sym (cong fst prop≡x≢0)) ¬¬Stable¬
  where
  open CommRingStr (snd k)

  0∉kˣ : ¬ 0r ∈ k ˣ
  0∉kˣ 0∈kˣ = PT.rec isProp⊥ (¬Fin0 ∘ fst) (k-local (λ{()}) 0∈kˣ)

  prop≡x≢0 : std-qc-open-prop x ≡ ((¬ x ≡ const 0r) , isProp¬ _)
  prop≡x≢0 =
    ⇒∶ PT.rec (isProp¬ _) (λ{ (i , xi∈kˣ) x≡0 → 0∉kˣ (subst (_∈ k ˣ) (funExt⁻ x≡0 i) xi∈kˣ)})
    ⇐∶ generalized-field-property k-local k-sqc x

is-qc-open→stable : {P : hProp ℓ} → is-qc-open P → ¬¬Stable ⟨ P ⟩
is-qc-open→stable {P = P} open-P =
  PT.rec (isProp→ (isProp⟨⟩ P))
         (λ{ (n , ∣x,P≡∣) → PT.rec (isProp→ (isProp⟨⟩ P))
                               (λ{ (x , P≡) → subst ¬¬Stable (sym (cong fst P≡)) (stable-std-qc-open-prop x)})
                               ∣x,P≡∣})
         open-P

```
