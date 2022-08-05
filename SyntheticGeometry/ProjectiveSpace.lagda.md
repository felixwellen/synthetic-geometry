Projective Space
================
Construct projective space as a quotient of 𝔸ⁿ⁺¹-{0}.
```agda
module SyntheticGeometry.ProjectiveSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_) renaming (ℙ to Powerset)

open import Cubical.Functions.Logic using (⇒∶_⇐∶_)

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

private variable ℓ : Level

module _ (k : CommRing ℓ) (n : ℕ) where
  module k = CommRingStr (snd k)

  𝔸ⁿ⁺¹ = FinVec ⟨ k ⟩ (n + 1)

  0𝔸ⁿ⁺¹ : 𝔸ⁿ⁺¹
  0𝔸ⁿ⁺¹ = replicateFinVec (n + 1) k.0r

  𝔸ⁿ⁺¹-0 = Σ[ x ∈ 𝔸ⁿ⁺¹ ] ¬ (x ≡ 0𝔸ⁿ⁺¹)

  linear-equivalent : (x y : 𝔸ⁿ⁺¹-0) → Type _
  linear-equivalent (x , _) (y , _) =
    Σ[ c ∈ ⟨ k ⟩ ] (c ∈ (k ˣ)) × ((i : Fin (n + 1)) → c k.· (x i) ≡ y i)

  linear-equivalence-sym : (x y : 𝔸ⁿ⁺¹-0) → linear-equivalent x y → linear-equivalent y x
  linear-equivalence-sym x y (c , c∈kˣ , cx≡y) =
    c⁻¹ ,
    Units.RˣInvClosed k c ,
    λ i → c⁻¹ k.· fst y i         ≡⟨ sym (cong (c⁻¹ k.·_) (cx≡y i)) ⟩
          c⁻¹ k.· (c k.· fst x i) ≡⟨ ·Assoc _ c _ ⟩
          (c⁻¹ k.· c) k.· fst x i ≡⟨ cong (k._· fst x i) (Units.·-linv k c) ⟩
          k.1r k.· fst x i        ≡⟨ ·IdL _  ⟩
          fst x i ∎
    where
      open k
      instance _ = c∈kˣ
      c⁻¹ = fst c∈kˣ

  ℙ : Type _
  ℙ = 𝔸ⁿ⁺¹-0 / linear-equivalent
```
Construct an open covering by affine schemes.
```agda

  U : (i : Fin (n + 1)) → ℙ → (qc-open-prop k)
  U i = SQ.rec
          (is-set-qc-open-prop k)
          (λ x → simple-qc-open-prop k ((fst x) i))
          λ x y x~y
            → qc-open-≡
                k _ _
                (⇒∶ (step2 x y x~y)
                 ⇐∶ step2 y x (linear-equivalence-sym x y x~y))
      where
        step1 : (u v w : ⟨ k ⟩) → (u ∈ k ˣ) → (v ∈ k ˣ) → u k.· v ≡ w → w ∈ k ˣ
        step1 u v w u∈kˣ v∈kˣ p = subst (_∈ k ˣ) p (Units.RˣMultClosed k u v)
          where
            instance
              _ = u∈kˣ
              _ = v∈kˣ
        step2 : (x y : _) → linear-equivalent x y → fst x i ∈ k ˣ → fst y i ∈ k ˣ
        step2 x y (c , c∈kˣ , cx≡y) xi∈kˣ = step1 c (fst x i) (fst y i) c∈kˣ xi∈kˣ (cx≡y i)

  covering : isLocal k → sqc-over-itself k → (p : ℙ) → ∃[ i ∈ Fin (n + 1) ] ⟨ fst (U i p) ⟩
  covering k-local k-sqc =
    SQ.elimProp
      (λ _ → isPropPropTrunc)
      λ x → generalized-field-property k k-local k-sqc (fst x) (snd x)
```
