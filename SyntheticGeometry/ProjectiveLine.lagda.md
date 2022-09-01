Facts about the projective line ℙ¹
==================================

```agda
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_; _⊆_) renaming (ℙ to Powerset)
open import Cubical.Foundations.Function

open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution

open import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Pushout as Pushout

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

module PushoutMaps
  where
  f g : 𝔸¹ˣ → ⟨ k ⟩
  f (x , _) = x
  g (_ , (x⁻¹ , _)) = x⁻¹

open PushoutMaps

ℙ¹-as-pushout : Type ℓ
ℙ¹-as-pushout =
  Pushout {A = 𝔸¹ˣ} {B = ⟨ k ⟩} {C = ⟨ k ⟩} f g

module Comparison
  where

  open CommRingStr (snd k)
  open Consequences k k-local
  open Units k

  -- More specific types for some operations.
  [_]ℙ¹ : 𝔸ⁿ⁺¹-0 1 → ℙ 1
  [_]ℙ¹ = [_]

  inl' inr' : ⟨ k ⟩ → ℙ¹-as-pushout
  inl' = inl
  inr' = inr

  inversion : 𝔸¹ˣ → 𝔸¹ˣ
  inversion (x , x-inv) = (x ⁻¹) , RˣInvClosed x
    where
    instance
      _ : x ∈ k ˣ
      _ = x-inv

  -- Just checking that this is definitional.
  g≡f∘inversion : (x : 𝔸¹ˣ) → g x ≡ f (inversion x)
  g≡f∘inversion x = refl

  isEquiv-inversion : isEquiv inversion
  isEquiv-inversion = involIsEquiv (λ x → Σ≡Prop (snd ∘ (k ˣ)) refl)

  isSet-ℙ¹-as-pushout : isSet ℙ¹-as-pushout
  isSet-ℙ¹-as-pushout =
    Pushout.preserveHLevelEmbedding
      f
      g
      {n = 0}
      isEmbedding-f
      (isEmbedding-∘ isEmbedding-f (isEquiv→isEmbedding isEquiv-inversion))
      is-set
      is-set
    where
    isEmbedding-f = snd (snd (Subset→Embedding (k ˣ)))

  module To
    where

    ι₀ ι₁ : ⟨ k ⟩ → 𝔸ⁿ⁺¹-0 1
    fst (ι₀ x) = λ{ zero → 1r ; one → x}
    snd (ι₀ x) ≡0 = 1≢0 (funExt⁻ ≡0 zero)
    -- (λ{ zero → 1r ; one → x }) , (λ ≡0 → 1≢0 (funExt⁻ ≡0 zero))
    ι₁ x = (λ{ zero → x ; one → 1r }) , (λ ≡0 → 1≢0 (funExt⁻ ≡0 one))
    -- TODO

    -- I think we will also need the converse...?
    path : (x y : ⟨ k ⟩) → x · y ≡ 1r → [ ι₀ x ]ℙ¹ ≡ [ ι₁ y ]ℙ¹
    path x y xy≡1 =
      let yx≡1 : y · x ≡ 1r
          yx≡1 = ·Comm y x ∙ xy≡1
      in eq/ _ _ {! (y , ((x , yx≡1) , {!funExt (λ{ zero → ·IdR y ; one → yx≡1 }) !})) !}

    to : ℙ¹-as-pushout → ℙ 1
    to (inl x) = [ ι₀ x ]ℙ¹
    to (inr x) = [ ι₁ x ]ℙ¹
    to (push (x , y , xy≡1) i) = path x y xy≡1 i

  module From
    where

    module _
      (xy : 𝔸ⁿ⁺¹ 1)
      where

      private
        x = xy zero
        y = xy one

      pre-pre-from-𝔸²-0 : (Σ[ i ∈ _ ] xy i ∈ k ˣ) → ℙ¹-as-pushout
      pre-pre-from-𝔸²-0 (zero , x-inv) = inl (x ⁻¹ · y) where instance _ = x-inv
      pre-pre-from-𝔸²-0 (one , y-inv) = inr (y ⁻¹ · x) where instance _ = y-inv

      pre-from-𝔸²-0 : (∃[ i ∈ _ ] xy i ∈ k ˣ) → ℙ¹-as-pushout
      pre-from-𝔸²-0 =
        PT.rec→Set
          isSet-ℙ¹-as-pushout
          pre-pre-from-𝔸²-0
          (λ{ (zero , _) (zero , _) → cong (λ x-inv → inl' (fst x-inv · y)) (snd ((k ˣ) x) _ _)
            ; (zero , x-inv) (one , y-inv) → {!!}
            ; (one , y-inv) (zero , x-inv) → {!!}
            ; (one , _) (one , _) → cong (λ y-inv → inr' (fst y-inv · x)) (snd ((k ˣ) y) _ _)})

    from-𝔸²-0 : 𝔸ⁿ⁺¹-0 1 → ℙ¹-as-pushout
    from-𝔸²-0 (xy , xy≢0) =
      pre-from-𝔸²-0 xy
        (generalized-field-property k-local k-sqc xy xy≢0)

    from : ℙ 1 → ℙ¹-as-pushout
    from = SQ.rec
      isSet-ℙ¹-as-pushout
      from-𝔸²-0
      λ{ (xy , xy≢0) (x'y' , x'y'≢0) xy~x'y' → {!!} }

  module From∘To
    where

    open From
    open To

    from-𝔸²-0∘ι₀ : (x : ⟨ k ⟩) → from-𝔸²-0 (ι₀ x) ≡ inl x
    from-𝔸²-0∘ι₀ x =
      PT.elim
        {P = λ existence → pre-from-𝔸²-0 (fst (ι₀ x)) existence ≡ inl x}
        (λ _ → isSet-ℙ¹-as-pushout _ _)
        (λ{ (zero , 1r-inv) →  -- Yes, 1r is invertible. We already knew that.
              let instance _ = 1r-inv in
              cong inl' (1r ⁻¹ · x  ≡⟨ cong (_· x) 1⁻¹≡1 ⟩
                         1r · x     ≡⟨ ·IdL x ⟩
                         x          ∎)
          ; (one , x-inv) →  -- Oooh, turns out x is also invertible.
              let instance _ = x-inv in
              inr (x ⁻¹ · 1r) ≡⟨ cong inr' (·IdR (x ⁻¹)) ⟩
              inr (x ⁻¹)      ≡⟨ sym (push (x , x-inv)) ⟩
              inl x           ∎})
        (generalized-field-property k-local k-sqc (fst (ι₀ x)) (snd (ι₀ x)))

    from-𝔸²-0∘ι₁ : (x : ⟨ k ⟩) → from-𝔸²-0 (ι₁ x) ≡ inr x
    from-𝔸²-0∘ι₁ = {!!}

    from∘to : (x : ℙ¹-as-pushout) → from (to x) ≡ x
    from∘to =
      Pushout.elimProp
        _
        (λ _ → isSet-ℙ¹-as-pushout _ _)
        from-𝔸²-0∘ι₀
        from-𝔸²-0∘ι₁
```
