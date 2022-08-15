(qc-)Open subsets
=================

A proposition is quasicompact (qc) open iff it is logically equivalent to
one of f₁,...,fₙ being invertible in the base ring.

```agda
{-# OPTIONS --safe #-}
module SyntheticGeometry.Open where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (_∈_)
  renaming (ℙ to Powerset; isSetℙ to isSetPowerset)

open import Cubical.Functions.Logic

open import Cubical.Data.Nat
open import Cubical.Data.Empty hiding () renaming (rec to ⊥-rec)
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Nullary.Base using (¬_)

open import SyntheticGeometry.Spec

private variable ℓ ℓ' : Level

module _ (k : CommRing ℓ) where
  contains-invertible : {n : ℕ} → FinVec ⟨ k ⟩ n → Type _
  contains-invertible v = Σ[ i ∈ Fin _ ] (v i) ∈ k ˣ

  std-qc-open-prop : {n : ℕ} → FinVec ⟨ k ⟩ n → hProp _
  std-qc-open-prop v = ∥ contains-invertible v ∥ₚ

  is-qc-open : hProp _ → Type _
  is-qc-open P = ∃[ n ∈ ℕ ] ∃[ v ∈ FinVec ⟨ k ⟩ n ] P ≡ (std-qc-open-prop v)

  qc-open-prop : Type _
  qc-open-prop = Σ[ P ∈ hProp _ ] is-qc-open P

  create-qc-open-prop : {n : ℕ} → FinVec ⟨ k ⟩ n → qc-open-prop
  create-qc-open-prop v = (std-qc-open-prop v) , ∣ _ , ∣ v , refl ∣₁ ∣₁

  simple-qc-open-prop : ⟨ k ⟩ → qc-open-prop
  simple-qc-open-prop x =
    ((x ∈ k ˣ) , snd ((k ˣ) x)) ,
    ∣ _ , ∣ replicateFinVec 1 x , step1 ∣₁ ∣₁
    where
      step1 : (x ∈ (k ˣ) , snd ((k ˣ) x)) ≡ std-qc-open-prop (replicateFinVec 1 x)
      step1 = ⇒∶ (λ x∈kˣ → ∣ Fin.zero , x∈kˣ ∣₁)
              ⇐∶ PT.elim (λ _ → snd ((k ˣ) x))
                           λ {(Fin.zero , x∈kˣ) → x∈kˣ;
                              ((Fin.suc x) , _)  → ⊥-rec (¬Fin0 x)
                             }

  is-set-qc-open-prop : isSet (qc-open-prop)
  is-set-qc-open-prop = isSetΣSndProp isSetHProp (λ _ → isPropPropTrunc)

  qc-open-≡ : (U V : qc-open-prop)
    → fst U ≡ fst V
    → U ≡ V
  qc-open-≡ U V = Σ≡Prop λ _ → isPropPropTrunc

  is-qc-open-subset : {X : Type ℓ} → Powerset X → hProp (ℓ-suc ℓ)
  is-qc-open-subset U = ∀[ x ] is-qc-open (U x) , isPropPropTrunc

  qc-opens-in : (X : Type ℓ') → Type _
  qc-opens-in X = X → qc-open-prop

  infixl 3 _∈ᵤ_
  _∈ᵤ_ : {X : Type ℓ'} → (x : X) → qc-opens-in X → Type _
  x ∈ᵤ U = fst (fst (U x))

  qc-open-as-type : {X : Type ℓ'} → qc-opens-in X → Type _
  qc-open-as-type {X = X} U = Σ[ x ∈ X ] x ∈ᵤ U


  is-finite-qc-open-cover : {n : ℕ}
    → (X : Type ℓ') → (U : Fin n → qc-opens-in X)
    → hProp _
  is-finite-qc-open-cover {n = n} X U =
    ∀[ x ∶ X ] ∃[ i ∶ Fin n ] fst (U i x)


```
