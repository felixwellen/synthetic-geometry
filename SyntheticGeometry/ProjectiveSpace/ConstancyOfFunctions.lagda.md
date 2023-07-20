Constancy of functions ℙⁿ → k
=============================
We show that all functions ℙⁿ → k are constant,
assuming that all functions ℙ¹ → k are constant
(which we did not formalize yet).

```agda
{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat as ℕ using (ℕ; _+_)
open import Cubical.Data.FinData

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing

open import Cubical.Relation.Nullary.Base using (¬_; yes; no)

import SyntheticGeometry.SQC

module SyntheticGeometry.ProjectiveSpace.ConstancyOfFunctions
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace.StandardPoints k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace.P0 k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace.LineThroughPoints k k-local k-sqc
```

The case n = 0 is simple.

```agda
module n=0-Case
  where

  all-functions-constant :
    (f : ℙ 0 → ⟨ k ⟩) →
    2-Constant f
  all-functions-constant f p q = cong f (isContr→isProp isContr-ℙ⁰ p q)
```

Let us now deduce the case n ≥ 1 from the case n = 1.

```agda
equal-on-distinct-points :
  ((f : ℙ 1 → ⟨ k ⟩) → 2-Constant f) →
  (n : ℕ) →
  (f : ℙ n → ⟨ k ⟩) →
  (p q : ℙ n) →
  ¬ (p ≡ q) →
  f p ≡ f q
equal-on-distinct-points ℙ¹-case n f p q p≢q =
  PT.rec
    (is-set _ _)
    (λ (g , hits-p , hits-q) →
      f p                ≡⟨ sym (cong f hits-p) ⟩
      f (g (ℙ¹.p zero))  ≡⟨ ℙ¹-case (f ∘ g) _ _ ⟩
      f (g (ℙ¹.p one))   ≡⟨ cong f hits-q ⟩
      f q                ∎)
    (line-through-points-exists p q p≢q)
  where
  open CommRingStr (str k) using (is-set)
  module ℙ¹ = StandardPoints {n = 1}

module n≥1-Case
  (n-1 : ℕ)
  where

  n = ℕ.suc n-1

  sucn≡n+1 : ℕ.suc n ≡ n + 1
  sucn≡n+1 = ℕ.+-comm 1 n

  zero',one',zero'≢one' =
    subst
      (λ n+1 → Σ[ z ∈ Fin n+1 ] Σ[ o ∈ Fin n+1 ] ¬ (z ≡ o))
      sucn≡n+1
      (zero , one , znots)

  zero' : Fin (n + 1)
  zero' = fst zero',one',zero'≢one'
  one' : Fin (n + 1)
  one' = fst (snd zero',one',zero'≢one')
  zero'≢one' : ¬ (zero' ≡ one')
  zero'≢one' = snd (snd zero',one',zero'≢one')

  open StandardPoints {n = n}
  p₀ = p zero'
  p₁ = p one'

  module _
    (ℙ¹-case : (f : ℙ 1 → ⟨ k ⟩) → 2-Constant f)
    (f : ℙ n → ⟨ k ⟩)
    where

    equal-on-distinct = equal-on-distinct-points ℙ¹-case n f

    fp₀≡fp₁ : f p₀ ≡ f p₁
    fp₀≡fp₁ = equal-on-distinct p₀ p₁ (zero'≢one' ∘ pᵢ≡pⱼ→i≡j)

    fp≡fp₀ : (p : _) → f p ≡ f p₀
    fp≡fp₀ p =
      PT.rec
        (is-set _ _)
        (λ (i , Uᵢ[p]) → case (discreteFin i zero') of
          λ{ (yes i≡zero') →
               equal-on-distinct p p₁ (λ p≡p₁ →
                 zero'≢one' (
                   zero'  ≡⟨ sym i≡zero' ⟩
                   i      ≡⟨ Uᵢ[pⱼ]→i≡j _ _ (subst (fst ∘ fst ∘ U n i) p≡p₁ Uᵢ[p]) ⟩
                   one'   ∎))
               ∙ sym fp₀≡fp₁
           ; (no i≢zero') →
               equal-on-distinct p p₀ (λ p≡p₀ →
                 i≢zero' (Uᵢ[pⱼ]→i≡j i zero' (subst (fst ∘ fst ∘ U n i) p≡p₀ Uᵢ[p])))
           })
        (covering n p)
      where
      open CommRingStr (str k) using (is-set)

    all-functions-constant : 2-Constant f
    all-functions-constant p q = fp≡fp₀ p ∙ sym (fp≡fp₀ q)
```

Here is the complete result.

```agda
all-functions-constant :
  {n : ℕ} →
  ((f : ℙ one → ⟨ k ⟩) → 2-Constant f) →
  (f : ℙ n → ⟨ k ⟩) →
  2-Constant f
all-functions-constant {ℕ.zero} _ = n=0-Case.all-functions-constant
all-functions-constant {ℕ.suc n-1} = n≥1-Case.all-functions-constant n-1
```
