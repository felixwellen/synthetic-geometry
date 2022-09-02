Facts about the projective line ℙ¹
==================================

```agda
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_; _⊆_) renaming (ℙ to Powerset)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.Involution

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
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

  𝔸² : Type ℓ
  𝔸² = 𝔸ⁿ⁺¹ 1

  𝔸²-0 : Type ℓ
  𝔸²-0 = 𝔸ⁿ⁺¹-0 1

  𝔸²-≡ :
    {xy x'y' : 𝔸²} →
    (xy zero ≡ x'y' zero) →
    (xy one ≡ x'y' one) →
    xy ≡ x'y'
  𝔸²-≡ x≡x' y≡y' = funExt (λ{ zero → x≡x' ; one → y≡y'})

  -- More specific types for some operations.
  [_]ℙ¹ : 𝔸²-0 → ℙ 1
  [_]ℙ¹ = [_]

  inl' inr' : ⟨ k ⟩ → ℙ¹-as-pushout
  inl' = inl
  inr' = inr

  -- The autoequivalence of 𝔸¹ˣ that turns f into g and vice versa.
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

  module To -- TODO: rename to Function
    where

    ι₀ ι₁ : ⟨ k ⟩ → 𝔸²-0
    fst (ι₀ x) = λ{ zero → 1r ; one → x}
    snd (ι₀ x) ≡0 = 1≢0 (funExt⁻ ≡0 zero)
    fst (ι₁ x) = λ{ zero → x ; one → 1r}
    snd (ι₁ x) ≡0 = 1≢0 (funExt⁻ ≡0 one)

    -- I think we will also need the converse...?
    path : (x y : ⟨ k ⟩) → x · y ≡ 1r → [ ι₀ x ]ℙ¹ ≡ [ ι₁ y ]ℙ¹
    path x y xy≡1 =
      let yx≡1 : y · x ≡ 1r
          yx≡1 = ·Comm y x ∙ xy≡1
      in eq/ _ _ ( (y , ((x , yx≡1) , funExt (λ{ zero → ·IdR y ; one → yx≡1 }) )) )

    to : ℙ¹-as-pushout → ℙ 1
    to (inl x) = [ ι₀ x ]ℙ¹
    to (inr x) = [ ι₁ x ]ℙ¹
    to (push (x , y , xy≡1) i) = path x y xy≡1 i

  open To

  -- TODO: "ϕ" ?
  isSurjection-ϕ : isSurjection to
  isSurjection-ϕ =
    SQ.elimProp
      (λ _ → PT.isPropPropTrunc)
      λ{ (xy , xy≢0) →
        PT.map
          (uncurry (inner (xy , xy≢0)))
          (generalized-field-property k-local k-sqc xy xy≢0)
      }
    where
    computation :
      (x y : ⟨ k ⟩) →
      {{x-inv : x ∈ k ˣ}} →
      let instance _ = x-inv in
      (x · (x ⁻¹ · y)) ≡ y
    computation x y =
      (x · (x ⁻¹ · y)  ≡⟨ ·Assoc _ _ _ ⟩
       x · x ⁻¹ · y    ≡⟨ cong (_· _) (·-rinv x) ⟩
       1r · y          ≡⟨ ·IdL y ⟩
       y               ∎)
    module _
      ((xy , xy≢0) : 𝔸²-0)
      where
      x = xy zero
      y = xy one

      inner : (i : Fin 2) → (xy i ∈ (k ˣ)) → fiber to [ xy , xy≢0 ]
      inner zero x-inv =
        let instance _ = x-inv in
          inl (x ⁻¹ · y)
        , eq/ (ι₀ (x ⁻¹ · y))
              (xy , xy≢0)
              (x , x-inv , 𝔸²-≡ (·IdR x) (computation x y))
      inner one y-inv =
        let instance _ = y-inv in
          inr (y ⁻¹ · x)
        , eq/ (ι₁ (y ⁻¹ · x))
              (xy , xy≢0)
              (y , y-inv , 𝔸²-≡ (computation y x) (·IdR y))

  isProp-≡→≡ : {q q' : ℙ 1} → {p p' : ℙ¹-as-pushout} → isProp (q ≡ q' → p ≡ p')
  isProp-≡→≡ = isProp→ (isSet-ℙ¹-as-pushout _ _)

  intersection-case :
    (x x' : ⟨ k ⟩) →
    [ ι₀ x ]ℙ¹ ≡ [ ι₁ x' ]ℙ¹ →
    inl' x ≡ inr' x'
  intersection-case x x' e =
    PT.rec
    (isSet-ℙ¹-as-pushout _ _)
    (λ{ (s , s-inv , s1x≡x'1) →
          push (x , x' , (x · x'        ≡⟨ ·Comm _ _ ⟩
                          x' · x        ≡⟨ cong (_· x) (sym (funExt⁻ s1x≡x'1 zero)) ⟩
                          (s · 1r) · x  ≡⟨ cong (_· x) (·IdR s) ⟩
                          s · x         ≡⟨ funExt⁻ s1x≡x'1 one ⟩
                          1r            ∎))
      })
    (ℙⁿ-effective-quotient 1 e)

  is-injective-ϕ : (p p' : ℙ¹-as-pushout) → to p ≡ to p' → p ≡ p'
  is-injective-ϕ =
    Pushout.elimProp
      (λ p → (p' : _) → to p ≡ to p' → p ≡ p')
      (λ _ → isPropΠ (λ _ → isProp-≡→≡))
      (λ x → Pushout.elimProp
        (λ p' → to (inl x) ≡ to p' → inl x ≡ p')
        (λ _ → isProp-≡→≡)
        (λ x' e → PT.rec
          (isSet-ℙ¹-as-pushout _ _)
          (λ{ (s , s-inv , s1x≡1x') →
            cong inl' (x             ≡⟨ sym (·IdL x) ⟩
                      1r · x         ≡⟨ cong (_· x) (sym (funExt⁻ s1x≡1x' zero))  ⟩
                      (s · 1r) · x   ≡⟨ cong (_· x) (·IdR s) ⟩
                      s · x          ≡⟨ funExt⁻ s1x≡1x' one ⟩
                      x'             ∎)
          })
          (ℙⁿ-effective-quotient 1 e))
        (λ x' → intersection-case x x')
      )
      (λ x → Pushout.elimProp
        (λ p' → to (inr x) ≡ to p' → inr x ≡ p')
        (λ _ → isProp-≡→≡)
        (λ x' → sym ∘ intersection-case x' x ∘ sym)
        (λ x' e → PT.rec
          (isSet-ℙ¹-as-pushout _ _)
          (λ{ (s , s-inv , sx1≡x'1) →
            cong inr' (x             ≡⟨ sym (·IdL x) ⟩
                      1r · x         ≡⟨ cong (_· x) (sym (funExt⁻ sx1≡x'1 one))  ⟩
                      (s · 1r) · x   ≡⟨ cong (_· x) (·IdR s) ⟩
                      s · x          ≡⟨ funExt⁻ sx1≡x'1 zero ⟩
                      x'             ∎)
          })
          (ℙⁿ-effective-quotient 1 e))
      )

  isEquiv-ϕ : isEquiv to
  isEquiv-ϕ =
    isEmbedding×isSurjection→isEquiv
      ( injEmbedding squash/ (λ {p} {p'} → is-injective-ϕ p p')
      , isSurjection-ϕ )


  --------------------------------------------------------------------------

  module From
    where

    module XY
      (xy : 𝔸ⁿ⁺¹ 1)
      where

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
          (λ{ (zero , x-inv) (zero , x-inv') → cong (λ inv → inl' (fst inv · y)) (snd ((k ˣ) x) x-inv x-inv')
            ; (zero , x-inv) (one , y-inv) → {!!}
            ; (one , y-inv) (zero , x-inv) → {!!}
            ; (one , y-inv) (one , y-inv') → cong (λ inv → inr' (fst inv · x)) (snd ((k ˣ) y) y-inv y-inv')})

    from-𝔸²-0 : 𝔸ⁿ⁺¹-0 1 → ℙ¹-as-pushout
    from-𝔸²-0 (xy , xy≢0) =
      XY.pre-from-𝔸²-0 xy
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
        {P = λ existence → XY.pre-from-𝔸²-0 (fst (ι₀ x)) existence ≡ inl x}
        (λ _ → isSet-ℙ¹-as-pushout _ _)
        (λ{ (zero , 1r-inv) →
              let instance _ = 1r-inv in
              cong inl' (1r ⁻¹ · x  ≡⟨ cong (_· x) 1⁻¹≡1 ⟩
                         1r · x     ≡⟨ ·IdL x ⟩
                         x          ∎)
          ; (one , x-inv) →
              let instance _ = x-inv in
              inr' (x ⁻¹ · 1r) ≡⟨ cong inr' (·IdR (x ⁻¹)) ⟩
              inr' (x ⁻¹)      ≡⟨ sym (push (x , x-inv)) ⟩
              inl' x           ∎})
        (generalized-field-property k-local k-sqc (fst (ι₀ x)) (snd (ι₀ x)))

    from-𝔸²-0∘ι₁ : (x : ⟨ k ⟩) → from-𝔸²-0 (ι₁ x) ≡ inr x
    from-𝔸²-0∘ι₁ x =
      PT.elim
        {P = λ existence → XY.pre-from-𝔸²-0 (fst (ι₁ x)) existence ≡ inr x}
        (λ _ → isSet-ℙ¹-as-pushout _ _)
        (λ{ (one , 1r-inv) →
              let instance _ = 1r-inv in
              cong inr' (1r ⁻¹ · x  ≡⟨ cong (_· x) 1⁻¹≡1 ⟩
                         1r · x     ≡⟨ ·IdL x ⟩
                         x          ∎)
          ; (zero , x-inv) →
              let instance _ = x-inv in
              inl' (x ⁻¹ · 1r) ≡⟨ cong inl' (·IdR (x ⁻¹)) ⟩
              inl' (x ⁻¹)      ≡⟨ push (x ⁻¹ , RˣInvClosed x) ⟩
              inr' x           ∎})
        (generalized-field-property k-local k-sqc (fst (ι₁ x)) (snd (ι₁ x)))

    from∘to : (x : ℙ¹-as-pushout) → from (to x) ≡ x
    from∘to =
      Pushout.elimProp
        _
        (λ _ → isSet-ℙ¹-as-pushout _ _)
        from-𝔸²-0∘ι₀
        from-𝔸²-0∘ι₁

  module To∘From
    where

    open From
    open To

    module _
      (xy : 𝔸ⁿ⁺¹ 1)
      where

      open XY xy

      to∘pre-pre-from-𝔸²-0 :
        (pair : Σ[ i ∈ _ ] xy i ∈ k ˣ) →
        to (pre-pre-from-𝔸²-0 pair) ≡ [ xy , {!!} ]ℙ¹
      to∘pre-pre-from-𝔸²-0 = {!!}


    to∘from-𝔸²-0 : (x : 𝔸ⁿ⁺¹-0 1) → to (from-𝔸²-0 x) ≡ [ x ]ℙ¹
    to∘from-𝔸²-0 (xy , xy≢0) =
      {!!}

    to∘from : (x : ℙ 1) → to (from (x)) ≡ x
    to∘from =
      SQ.elimProp
        (λ _ → squash/ _ _)
        to∘from-𝔸²-0
```
