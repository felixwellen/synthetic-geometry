Facts about the projective line ℙ¹
==================================

```agda
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_; _⊆_) renaming (ℙ to Powerset)
open import Cubical.Foundations.Function

open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout

open import Cubical.Data.FinData
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing

import SyntheticGeometry.SQC

module SyntheticGeometry.ProjectiveLine
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.Spec k
open import SyntheticGeometry.Open k
open import SyntheticGeometry.Affine k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open SyntheticGeometry.SQC k
```

Exhibit ℙ¹ as a pushout of two copies of 𝔸¹.

```agda

𝔸¹ˣ : Type ℓ
𝔸¹ˣ = Σ[ x ∈ ⟨ k ⟩ ] x ∈ k ˣ

ℙ¹-as-pushout : Type ℓ
ℙ¹-as-pushout =
  Pushout {A = 𝔸¹ˣ} {B = ⟨ k ⟩} {C = ⟨ k ⟩}
    (λ (x , _) → x)
    λ (_ , (x⁻¹ , _)) → x⁻¹

module Comparison
  where

  open CommRingStr (snd k)
  open Consequences k k-local

  module To
    where

    ι₀ ι₁ : ⟨ k ⟩ → ℙ 1
    ι₀ x = [ (λ{ zero → 1r ; one → x }) , (λ ≡0 → 1≢0 (funExt⁻ ≡0 zero)) ]
    ι₁ x = [ (λ{ zero → x ; one → 1r }) , (λ ≡0 → 1≢0 (funExt⁻ ≡0 one)) ]

    -- I think we will also need the converse...?
    path : (x y : ⟨ k ⟩) → x · y ≡ 1r → ι₀ x ≡ ι₁ y
    path x y xy≡1 =
      let yx≡1 : y · x ≡ 1r
          yx≡1 = ·Comm y x ∙ xy≡1
      in eq/ _ _ (y , ((x , yx≡1) , funExt (λ{ zero → ·IdR y ; one → yx≡1 })))

    to : ℙ¹-as-pushout → ℙ 1
    to (inl x) = ι₀ x
    to (inr x) = ι₁ x
    to (push (x , y , xy≡1) i) = path x y xy≡1 i
```
