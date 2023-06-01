Existence of lines through given points in projective space
===========================================================
Given two distinct points in ℙⁿ,
we show that there exists a line in ℙⁿ interpolating between these points,
that is, a function ℙ¹ → ℙⁿ that hits the points.

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

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat as ℕ hiding (_+_)
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

module _
  {n : ℕ}
  (a b : FinVec ⟨ k ⟩ (n ℕ.+ 1))
  (a≠b : a ≡ b → ⊥)
  where

  private module 𝔸ⁿ⁺¹ = LeftModuleStr (str (FinVecLeftModule (CommRing→Ring k) {n = n ℕ.+ 1}))
  open 𝔸ⁿ⁺¹

  f : ℙ 1 → ℙ n
  f = SQ.rec squash/
    (λ (x , x≠0) → [ ((x zero ⋆ a) + (x one ⋆ b)) , (λ ≡0 → {!!}) ])
    λ (x , _) (y , _) (c , c-inv , r) → eq/ _ _ (c , c-inv , (
        (c ⋆ ((x zero ⋆ a) + (x one ⋆ b)))        ≡⟨ {!!} ⟩
        ((c ⋆ (x zero ⋆ a)) + (c ⋆ (x one ⋆ b)))  ≡⟨ {!!} ⟩
        ((y zero ⋆ a) + (y one ⋆ b))              ∎ ))
