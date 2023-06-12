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
open import Cubical.Data.Empty

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing
open import Cubical.Algebra.Module
open import Cubical.Algebra.Module.Instances.FinVec
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra.Instances using (polynomialAlgFP)

open import Cubical.Relation.Nullary.Base using (¬_)
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

module _
  {n : ℕ}
  ((a , a≠0) (b , b≠0) : 𝔸ⁿ⁺¹-0 n)
  ([a]≠[b] : [ a , a≠0 ] ≡ [ b , b≠0 ] → ⊥)
  where

  private
    module k = CommRingStr (snd k)
    module 𝔸ⁿ⁺¹ = LeftModuleStr (str (FinVecLeftModule (CommRing→Ring k) {n = n ℕ.+ 1}))
  open k using (_·_)
  open 𝔸ⁿ⁺¹

  module Construction
    ((x , x≠0) : 𝔸ⁿ⁺¹-0 1)
    where

    value : 𝔸ⁿ⁺¹ n
    value = (x zero ⋆ a) + (x one ⋆ b)

    non-zero : value ≡ 0𝔸ⁿ⁺¹ n → ⊥
    non-zero = {!!}

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
