Standard points of projective space
===================================

```agda
{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_)
open import Cubical.Foundations.Function

open import Cubical.HITs.SetQuotients as SQ using ([_])
open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.FinData
import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing
open import Cubical.Algebra.Ring using (module RingTheory)

open import Cubical.Relation.Nullary.Base using (¬_; yes; no)

import SyntheticGeometry.SQC

module SyntheticGeometry.ProjectiveSpace.StandardPoints
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open import SyntheticGeometry.ProjectiveSpace.CharacterizationOfLinearEquivalence k k-local k-sqc
```

Here are certain "standard" points of projective space.

```agda
module StandardPoints
  {n : ℕ}
  where

  open CommRingStr (snd k)

  -- TODO: define standard basis vectors in the cubical library and use those instead
  standard-basis-vector : Fin (n ℕ.+ 1) → FinVec ⟨ k ⟩ (n ℕ.+ 1)
  standard-basis-vector i j =
    case (discreteFin i j) of
      λ{ (yes _) → 1r
       ; (no _) → 0r
       }

  standard-basis-vector-1-entry : (i : _) → standard-basis-vector i i ≡ 1r
  standard-basis-vector-1-entry i with (discreteFin i i)
  ... | yes _ = refl
  ... | no i≠i = ⊥.rec (i≠i refl)

  standard-basis-vector-0-entry : (i j : _) → ¬ (i ≡ j) → standard-basis-vector i j ≡ 0r
  standard-basis-vector-0-entry i j i≢j with (discreteFin i j)
  ... | yes i≡j = ⊥.elim (i≢j i≡j)
  ... | no _ = refl

  standard-basis-vector-≢0 : (i : _) → ¬ standard-basis-vector i ≡ 0𝔸ⁿ⁺¹ n
  standard-basis-vector-≢0 i ≡0 =
    1≢0 (
      1r                         ≡⟨ sym (standard-basis-vector-1-entry i) ⟩
      standard-basis-vector i i  ≡⟨ funExt⁻ ≡0 i ⟩
      0r                         ∎ )
    where
    open Consequences k k-local

  p : Fin (n ℕ.+ 1) → ℙ n
  p i = [ standard-basis-vector i , standard-basis-vector-≢0 i ]
```

A lemma for recognizing standard points.

```agda
  module _
    (i : Fin (n ℕ.+ 1))
    ((x , x≢0) : 𝔸ⁿ⁺¹-0 n)
    where

    recognize-standard-point : ((j : _) → ¬ (j ≡ i) → x j ≡ 0r) → [ x , x≢0 ] ≡ p i
    recognize-standard-point x≈0 =
      sym (SQ.eq/ _ _
        (char
          (e i , standard-basis-vector-≢0 i)
          (x , x≢0)
          (x i)
          (funExt (λ j → case (discreteFin i j) return const _ of
            λ{ (yes i≡j) →
                 x i · e i j  ≡⟨ cong₂ (_·_) (cong x i≡j) (cong₂ e i≡j refl) ⟩
                 x j · e j j  ≡⟨ cong (x j ·_) (standard-basis-vector-1-entry j) ⟩
                 x j · 1r     ≡⟨ ·IdR _ ⟩
                 x j          ∎
             ; (no i≢j) →
                 x i · e i j  ≡⟨ cong (x i ·_) (standard-basis-vector-0-entry i j i≢j) ⟩
                 x i · 0r     ≡⟨ 0RightAnnihilates _ ⟩
                 0r           ≡⟨ sym (x≈0 j (i≢j ∘ sym)) ⟩
                 x j          ∎
             }))))
      where
      e = standard-basis-vector
      open RingTheory (CommRing→Ring k)

```

Relation with the standard open cover of ℙⁿ:
The i-th standard point lies only in the i-th standard open.

```agda
  Uᵢ[pᵢ] : (i : _) → ⟨ fst (U _ i (p i)) ⟩
  Uᵢ[pᵢ] i =
    subst (_∈ (k ˣ))
      (sym (standard-basis-vector-1-entry i))
      RˣContainsOne
    where
    open Units k

  Uᵢ[pⱼ]→i≡j : (i j : _) → ⟨ fst (U _ i (p j)) ⟩ → i ≡ j
  Uᵢ[pⱼ]→i≡j i j Uᵢ[pⱼ] =
    case (discreteFin i j) return const (i ≡ j) of
      λ{ (yes i≡j) → i≡j
       ; (no i≢j) → ⊥.elim (1≢0
           let
           j≢i : ¬ (j ≡ i)
           j≢i j≡i = i≢j (sym j≡i)
           instance
             0-inv : 0r ∈ k ˣ
             0-inv =
               subst (_∈ (k ˣ))
                 (standard-basis-vector-0-entry j i j≢i)
                 Uᵢ[pⱼ]
           in
           1r          ≡⟨ sym (·-rinv 0r) ⟩
           0r · 0r ⁻¹  ≡⟨ 0LeftAnnihilates _ ⟩
           0r          ∎)
       }
    where
    open Units k
    open Consequences k k-local
    open RingTheory (CommRing→Ring k)
```

The standard points are pairwise distinct.

```agda
  pᵢ≡pⱼ→i≡j : {i j : _} → p i ≡ p j → i ≡ j
  pᵢ≡pⱼ→i≡j {i} {j} pi≡pj = Uᵢ[pⱼ]→i≡j i j (subst (fst ∘ fst ∘ U n i) pi≡pj (Uᵢ[pᵢ] i))
```
