A proposition is quasicompact open iff it is logically equivalent to
to one of f₁,...,fₙ being invertible in the base ring.
```agda
module SyntheticGeometry.Open where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset using (_∈_)
  renaming (ℙ to Powerset; isSetℙ to isSetPowerset)

open import Cubical.Functions.Logic

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Nullary.Base using (¬_)

open import SyntheticGeometry.Spec

private variable ℓ : Level

module _ (k : CommRing ℓ) where
  contains-invertible : {n : ℕ} → FinVec ⟨ k ⟩ n → Type _
  contains-invertible v = Σ[ i ∈ Fin _ ] (v i) ∈ k ˣ

  std-qc-open-prop : {n : ℕ} → FinVec ⟨ k ⟩ n → hProp _
  std-qc-open-prop v = ∥ contains-invertible v ∥₁ , isPropPropTrunc

  is-qc-open : hProp _ → Type _
  is-qc-open P = ∃[ n ∈ ℕ ] ∃[ v ∈ FinVec ⟨ k ⟩ n ] P ≡ (std-qc-open-prop v)

  is-qc-open-subset : {X : Type ℓ} → Powerset X → Type _
  is-qc-open-subset {X = X} U = (x : X) → is-qc-open (U x)

  is-prop-qc-open-subset : {X : Type ℓ} → (P : Powerset X) → isProp (is-qc-open-subset P)
  is-prop-qc-open-subset P = isPropΠ λ _ → isPropPropTrunc

  qc-opens-in : (X : Type ℓ) → Type _
  qc-opens-in X = Σ[ U ∈ Powerset X ] is-qc-open-subset U

  is-set-qc-opens : (X : Type ℓ) → isSet (qc-opens-in X)
  is-set-qc-opens X = isSetΣSndProp isSetPowerset (λ U → is-prop-qc-open-subset U)
```
