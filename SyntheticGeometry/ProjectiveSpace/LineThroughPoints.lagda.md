Existence of lines through given points in projective space
===========================================================
Given two distinct points in ℙⁿ,
we show that there exists a line in ℙⁿ interpolating between these points,
that is, a function ℙ¹ → ℙⁿ that hits the points.

Note:
We could alternatively show that
(1) injective maps of vector spaces induce maps of projective spaces and
(2) two nonzero vectors are linearly independent iff they represent different points in ℙⁿ.

```agda
-- TODO: clean up imports
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_; _⊆_; ⊆-extensionality) renaming (ℙ to Powerset)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed using (_→∙_)
open import Cubical.Foundations.Pointed.Homogeneous using (isHomogeneousDiscrete)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.Function

open import Cubical.Structures.Pointed using (pointed-sip)

open import Cubical.Functions.Logic using (⇒∶_⇐∶_)
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.Image

import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat as ℕ using (ℕ; suc)
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing
open import Cubical.Algebra.Ring using (module RingTheory)
open import Cubical.Algebra.Module
open import Cubical.Algebra.Module.Instances.FinVec
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra.Instances using (polynomialAlgFP)

open import Cubical.Relation.Nullary.Base using (¬_; yes; no)
open import Cubical.Relation.Binary

open import Cubical.Tactics.CommRingSolver.Reflection

import SyntheticGeometry.SQC

module SyntheticGeometry.ProjectiveSpace.LineThroughPoints
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.ProjectiveSpace k k-local k-sqc
open import SyntheticGeometry.SQC.Consequences k k-local k-sqc
```

We need a slight reformulation of linear equivalence between non-zero vectors.

```agda
module CharacterizationOfLinearEquivalence
  {n : ℕ}
  ((a , a≠0) (b , b≠0) : 𝔸ⁿ⁺¹-0 n)
  where

  open LeftModuleStr (str (FinVecLeftModule (CommRing→Ring k) {n = n ℕ.+ 1}))
  open Units k

  char : (c : ⟨ k ⟩) → c ⋆ a ≡ b → linear-equivalent _ a b
  char c ca≡b = c , c-inv , ca≡b
    where
      c-inv : c ∈ k ˣ
      c-inv = PT.rec
        (str ((k ˣ) c))
        (λ (i , bi-inv) → fst (RˣMultDistributing c (a i) (subst (_∈ k ˣ) (sym (funExt⁻ ca≡b i)) bi-inv)))
        (generalized-field-property b b≠0)


private
  [_] : {n : ℕ} → 𝔸ⁿ⁺¹-0 n → ℙ n
  [_] = SQ.[_]
```

Here are certain "standard" points of projective space.

```agda
module StandardPoints
  {n : ℕ}
  where

  open CommRingStr (snd k)

  -- TODO: define standard basis vectors in the cubical libraries and use those instead
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

  p : Fin (n ℕ.+ 1) → ℙ n
  p i =
    [ standard-basis-vector i ,
      (λ ≡0 → 1≢0 (
        1r                         ≡⟨ sym (standard-basis-vector-1-entry i) ⟩
        standard-basis-vector i i  ≡⟨ funExt⁻ ≡0 i ⟩
        0r                         ∎ )) ]
    where
    open Consequences k k-local
```

We now construct the line through two distinct points in projective space,
assuming that fixed representatives for the points are given.

```agda
module _
  {n : ℕ}
  ((a , a≠0) (b , b≠0) : 𝔸ⁿ⁺¹-0 n)
  ([a]≠[b] : [ a , a≠0 ] ≡ [ b , b≠0 ] → ⊥)
  where

  private
    module k = CommRingStr (snd k)
    𝔸ⁿ⁺¹-as-module = FinVecLeftModule (CommRing→Ring k) {n = n ℕ.+ 1}
    module 𝔸ⁿ⁺¹ = LeftModuleStr (str 𝔸ⁿ⁺¹-as-module)
  open k using (_·_; -_; 0r; 1r)
  open 𝔸ⁿ⁺¹ hiding (-_)

  module Construction
    ((x , x≠0) : 𝔸ⁿ⁺¹-0 1)
    where

    x₀ = x zero
    x₁ = x one

    value : 𝔸ⁿ⁺¹ n
    value = (x₀ ⋆ a) + (x₁ ⋆ b)

    module _
      (value≡0 : value ≡ 0𝔸ⁿ⁺¹ n)
      where

      private
        module k-Th = RingTheory (CommRing→Ring k)

      open Units k
      open CharacterizationOfLinearEquivalence
      open AbGroupTheory (LeftModule→AbGroup 𝔸ⁿ⁺¹-as-module)
      open ModuleTheory _ 𝔸ⁿ⁺¹-as-module

      x₀-inv→[b]≡[a] : (x₀ ∈ k ˣ) → [ b , b≠0 ] ≡ [ a , a≠0 ]
      x₀-inv→[b]≡[a] x₀-inv =
        SQ.eq/ _ _ (char (b , b≠0) (a , a≠0) (x₀⁻¹ · (- x₁)) (
          ((x₀⁻¹ · (- x₁)) ⋆ b)      ≡⟨ ⋆Assoc _ _ _ ⟩
          (x₀⁻¹ ⋆ ((- x₁) ⋆ b))      ≡⟨ cong (x₀⁻¹ ⋆_) (
            ((- x₁) ⋆ b)           ≡⟨ cong (_⋆ b) (k-Th.-IsMult-1 _) ⟩
            (((- 1r) · x₁) ⋆ b)    ≡⟨ ⋆Assoc _ _ _ ⟩
            ((- 1r) ⋆ (x₁ ⋆ b))    ≡⟨ minusByMult _ ⟩
            (𝔸ⁿ⁺¹.- x₁ ⋆ b)       ≡⟨ sym (implicitInverse (+Comm _ _ ∙ value≡0)) ⟩
            (x₀ ⋆ a)               ∎ ) ⟩
          (x₀⁻¹ ⋆ (x₀ ⋆ a))          ≡⟨ sym (⋆Assoc _ _ _) ⟩
          ((x₀⁻¹ · x₀) ⋆ a)          ≡⟨ cong (_⋆ a) (·-linv _) ⟩
          (1r ⋆ a)                   ≡⟨ ⋆IdL _ ⟩
          a                          ∎ ))
        where
        instance
          _ = x₀-inv
        x₀⁻¹ = x₀ ⁻¹

      x₁-inv→[a]≡[b] : (x₁ ∈ k ˣ) → [ a , a≠0 ] ≡ [ b , b≠0 ]
      x₁-inv→[a]≡[b] x₁-inv =
        SQ.eq/ _ _ (char (a , a≠0) (b , b≠0) (x₁⁻¹ · (- x₀)) (
          ((x₁⁻¹ · (- x₀)) ⋆ a)      ≡⟨ ⋆Assoc _ _ _ ⟩
          (x₁⁻¹ ⋆ ((- x₀) ⋆ a))      ≡⟨ cong (x₁⁻¹ ⋆_) (
            ((- x₀) ⋆ a)           ≡⟨ cong (_⋆ a) (k-Th.-IsMult-1 _) ⟩
            (((- 1r) · x₀) ⋆ a)    ≡⟨ ⋆Assoc _ _ _ ⟩
            ((- 1r) ⋆ (x₀ ⋆ a))    ≡⟨ minusByMult _ ⟩
            (𝔸ⁿ⁺¹.- x₀ ⋆ a)       ≡⟨  sym (implicitInverse value≡0) ⟩
            (x₁ ⋆ b)               ∎ ) ⟩
          (x₁⁻¹ ⋆ (x₁ ⋆ b))          ≡⟨ sym (⋆Assoc _ _ _) ⟩
          ((x₁⁻¹ · x₁) ⋆ b)          ≡⟨ cong (_⋆ b) (·-linv _) ⟩
          (1r ⋆ b)                   ≡⟨ ⋆IdL _ ⟩
          b                          ∎ ))
        where
        instance
          _ = x₁-inv
        x₁⁻¹ = x₁ ⁻¹

      non-zero : ⊥
      non-zero =
        PT.rec
          isProp⊥
          (λ{ (zero , x₀-inv) → [a]≠[b] (sym (x₀-inv→[b]≡[a] x₀-inv))
            ; (one , x₁-inv) → [a]≠[b] (x₁-inv→[a]≡[b] x₁-inv)
            })
          (generalized-field-property x x≠0)

  open Construction

  private
    respects-linear-equivalence :
      (x : 𝔸ⁿ⁺¹-0 1) →
      (y : 𝔸ⁿ⁺¹-0 1) →
      linear-equivalent 1 (fst x) (fst y) →
      linear-equivalent n (value x) (value y)
    respects-linear-equivalence (x , x≠0) (y , y≠0) (c , c-inv , cx≡y) =
      c , c-inv ,
      ( (c ⋆ ((x zero ⋆ a) + (x one ⋆ b)))        ≡⟨ ⋆DistR+ _ _ _ ⟩
        ((c ⋆ (x zero ⋆ a)) + (c ⋆ (x one ⋆ b)))  ≡⟨ sym (cong₂ _+_ (⋆Assoc _ _ _) (⋆Assoc _ _ _)) ⟩
        (((c · x zero) ⋆ a) + ((c · x one) ⋆ b))  ≡⟨ cong₂ _+_ (cong (_⋆ a) (funExt⁻ cx≡y zero))
                                                               (cong (_⋆ b) (funExt⁻ cx≡y one)) ⟩
        ((y zero ⋆ a) + (y one ⋆ b))              ∎ )

  line-through-points : ℙ 1 → ℙ n
  line-through-points = SQ.rec SQ.squash/
    (λ x → [ value x , non-zero x ])
    λ x y rel → SQ.eq/ _ _ (respects-linear-equivalence x y rel)

  open StandardPoints {n = 1}
  open ModuleTheory _ 𝔸ⁿ⁺¹-as-module

  line-hits-point-0 : line-through-points (p zero) ≡ [ a , a≠0 ]
  line-hits-point-0 = cong [_] (Σ≡Prop (λ _ → isProp→ isProp⊥) (
    ((1r ⋆ a) + (0r ⋆ b))  ≡⟨ cong₂ _+_ (⋆IdL _) (⋆AnnihilL _) ⟩
    (a + 0m)               ≡⟨ +IdR _ ⟩
    a                      ∎))

  line-hits-point-1 : line-through-points (p one) ≡ [ b , b≠0 ]
  line-hits-point-1 = cong [_] (Σ≡Prop (λ _ → isProp→ isProp⊥) ((
    ((0r ⋆ a) + (1r ⋆ b))  ≡⟨ cong₂ _+_ (⋆AnnihilL _) (⋆IdL _) ⟩
    (0m + b)               ≡⟨ +IdL _ ⟩
    b                      ∎)))
```

If we are given distinct points (but not representatives),
we can still derive the existence of a line through these points.

```agda
-- TODO
```
