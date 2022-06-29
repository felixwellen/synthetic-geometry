Projective Space
================
Construct projective space as a quotient of 𝔸ⁿ⁺¹.
```agda
module SyntheticGeometry.ProjectiveSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_)

open import Cubical.HITs.SetQuotients
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Nullary.Base using (¬_)

open import SyntheticGeometry.Spec

private variable ℓ : Level

module _ (k : CommRing ℓ) (n : ℕ) where
  module 𝔸¹ = CommRingStr (snd k)

  𝔸ⁿ⁺¹ = FinVec ⟨ k ⟩ (n + 1)

  0𝔸ⁿ⁺¹ : 𝔸ⁿ⁺¹
  0𝔸ⁿ⁺¹ = replicateFinVec (n + 1) 𝔸¹.0r

  𝔸ⁿ⁺¹-0 = Σ[ x ∈ 𝔸ⁿ⁺¹ ] ¬ (x ≡ 0𝔸ⁿ⁺¹)

  linear-equivalent : (x y : 𝔸ⁿ⁺¹-0) → Type _
  linear-equivalent (x , _) (y , _) =
    Σ[ c ∈ ⟨ k ⟩ ] (c ∈ (k ˣ)) × ((i : Fin (n + 1)) → c 𝔸¹.· (x i) ≡ y i)

  ℙ : Type _
  ℙ = 𝔸ⁿ⁺¹-0 / linear-equivalent
```
