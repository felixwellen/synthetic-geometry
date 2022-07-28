Projective Space
================
Construct projective space as a quotient of 𝔸ⁿ⁺¹.
```agda
module SyntheticGeometry.ProjectiveSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_) renaming (ℙ to Powerset)
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Logic using (⇒∶_⇐∶_)
open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing

open import Cubical.Relation.Nullary.Base using (¬_)

open import SyntheticGeometry.Spec
open import SyntheticGeometry.Open
open import SyntheticGeometry.SQC

open import Cubical.Tactics.CommRingSolver.Reflection

private variable ℓ : Level

module _ (k : CommRing ℓ) (n : ℕ) where
  module k = CommRingStr (snd k)

  𝔸ⁿ⁺¹ = FinVec ⟨ k ⟩ (n + 1)

  0𝔸ⁿ⁺¹ : 𝔸ⁿ⁺¹
  0𝔸ⁿ⁺¹ = replicateFinVec (n + 1) k.0r

  𝔸ⁿ⁺¹-0 = Σ[ x ∈ 𝔸ⁿ⁺¹ ] ¬ (x ≡ 0𝔸ⁿ⁺¹)

  linear-equivalent : (x y : 𝔸ⁿ⁺¹) → Type _
  linear-equivalent x y =
    Σ[ c ∈ ⟨ k ⟩ ] (c ∈ (k ˣ)) × ((i : Fin (n + 1)) → c k.· (x i) ≡ y i)

  linear-equivalence-sym : (x y : 𝔸ⁿ⁺¹) → linear-equivalent x y → linear-equivalent y x
  linear-equivalence-sym x y (c , c∈kˣ , cx≡y) =
    c⁻¹ ,
    Units.RˣInvClosed k c ,
    λ i → c⁻¹ k.· y i          ≡⟨ sym (cong (c⁻¹ k.·_) (cx≡y i)) ⟩
          c⁻¹ k.· (c k.· x i)  ≡⟨ ·Assoc _ c _ ⟩
          (c⁻¹ k.· c) k.· x i  ≡⟨ cong (k._· x i) (Units.·-linv k c) ⟩
          k.1r k.· x i         ≡⟨ ·IdL _  ⟩
          x i                  ∎
    where
      open k
      instance _ = c∈kˣ
      c⁻¹ = fst c∈kˣ

  ℙ : Type _
  ℙ = 𝔸ⁿ⁺¹-0 / (λ x y → linear-equivalent (fst x) (fst y))
```
Construct an open covering by affine schemes.
```agda
  module _
    (i : Fin (n + 1))
    where

    U : ℙ → (qc-open-prop k)
    U = SQ.rec
            (is-set-qc-open-prop k)
            (λ x → simple-qc-open-prop k ((fst x) i))
            λ x y x~y
              → qc-open-≡
                  k _ _
                  (⇒∶ (step2 (fst x) (fst y) x~y)
                   ⇐∶ step2 (fst y) (fst x) (linear-equivalence-sym _ _ x~y))
        where
          step1 : (u v w : ⟨ k ⟩) → (u ∈ k ˣ) → (v ∈ k ˣ) → u k.· v ≡ w → w ∈ k ˣ
          step1 u v w u∈kˣ v∈kˣ p = subst (_∈ k ˣ) p (Units.RˣMultClosed k u v)
            where
              instance
                _ = u∈kˣ
                _ = v∈kˣ
          step2 : (x y : _) → linear-equivalent x y → x i ∈ k ˣ → y i ∈ k ˣ
          step2 x y (c , c∈kˣ , cx≡y) xi∈kˣ = step1 c (x i) (y i) c∈kˣ xi∈kˣ (cx≡y i)

    embedded-𝔸ⁿ : Type ℓ
    embedded-𝔸ⁿ = Σ[ x ∈ 𝔸ⁿ⁺¹ ] x i ≡ k.1r

    module _ (k-local : isLocal k) where
      ι : embedded-𝔸ⁿ → ℙ
      ι (x , xi≡1) = [ x , (λ x≡0 → 1≢0 (sym xi≡1 ∙ cong (λ x → x i) x≡0)) ]
        where
        open Consequences k k-local

      ι-injective : (x y : embedded-𝔸ⁿ) → ι x ≡ ι y → x ≡ y
      ι-injective (x , xi≡1) (y , yi≡1) ιx≡ιy =
        Σ≡Prop
          (λ _ → k.is-set _ _)
          (funExt (λ j → lineq→≡ (effective (λ _ _ → {!!}) {!!} _ _ ιx≡ιy) j))
        where
        lineq→≡ : linear-equivalent x y → (j : _) → x j ≡ y j
        lineq→≡ (c , _ , cx≡y) j =
          x j           ≡⟨ sym (·IdL _) ⟩
          1r k.· x j    ≡⟨ cong (k._· _) (sym c≡1) ⟩
          c k.· x j     ≡⟨ cx≡y j ⟩
          y j           ∎
          where
          open k
          c≡1 : c ≡ k.1r
          c≡1 =
            c           ≡⟨ sym (·IdR _) ⟩
            c k.· 1r    ≡⟨ cong (_ k.·_) (sym xi≡1) ⟩
            c k.· x i   ≡⟨ cx≡y i ⟩
            y i         ≡⟨ yi≡1 ⟩
            1r          ∎

  covering : isLocal k → sqc-over-itself k → (p : ℙ) → ∃[ i ∈ Fin (n + 1) ] ⟨ fst (U i p) ⟩
  covering k-local k-sqc =
    SQ.elimProp
      (λ _ → isPropPropTrunc)
      λ x → generalized-field-property k k-local k-sqc (fst x) (snd x)
```
