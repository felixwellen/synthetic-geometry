Projective Space
================
Construct projective space as a quotient of 𝔸ⁿ⁺¹-{0}.

```agda
module SyntheticGeometry.ProjectiveSpace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Powerset using (_∈_) renaming (ℙ to Powerset)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed using (_→∙_)
open import Cubical.Foundations.Pointed.Homogeneous using (isHomogeneousDiscrete)
open import Cubical.Foundations.Univalence using (pathToEquiv)

open import Cubical.Structures.Pointed using (pointed-sip)

open import Cubical.Functions.Logic using (⇒∶_⇐∶_)
open import Cubical.Functions.Embedding

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat using (ℕ; _+_; +-comm)
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.LocalRing
open import Cubical.Algebra.Module
open import Cubical.Algebra.Module.Instances.FinVec

open import Cubical.Relation.Nullary.Base using (¬_)
open import Cubical.Relation.Binary

open import Cubical.Tactics.CommRingSolver.Reflection

open import SyntheticGeometry.Spec
open import SyntheticGeometry.Open
open import SyntheticGeometry.SQC

private variable ℓ : Level

module _ (k : CommRing ℓ) (n : ℕ) where
  module k = CommRingStr (snd k)
  module 𝔸ⁿ⁺¹ = LeftModuleStr (snd (FinVecLeftModule (CommRing→Ring k) {n = n + 1}))
  open k hiding (_+_)
  open 𝔸ⁿ⁺¹ hiding (_+_)
  open Units k

  𝔸ⁿ⁺¹ = FinVec ⟨ k ⟩ (n + 1)

  0𝔸ⁿ⁺¹ : 𝔸ⁿ⁺¹
  0𝔸ⁿ⁺¹ = replicateFinVec (n + 1) 0r

  𝔸ⁿ⁺¹-0 = Σ[ x ∈ 𝔸ⁿ⁺¹ ] ¬ (x ≡ 0𝔸ⁿ⁺¹)

  linear-equivalent : (x y : 𝔸ⁿ⁺¹) → Type _
  linear-equivalent x y =
    Σ[ c ∈ ⟨ k ⟩ ] (c ∈ (k ˣ)) × (c ⋆ x ≡ y)

  module _ where
    open BinaryRelation
    open isEquivRel

    isEquivRel-lin-eq : isEquivRel linear-equivalent

    reflexive isEquivRel-lin-eq x = 1r , RˣContainsOne , (⋆IdL _)

    symmetric isEquivRel-lin-eq x y (c , c∈kˣ , cx≡y) =
      c⁻¹ ,
      Units.RˣInvClosed k c ,
      ( c⁻¹ ⋆ y          ≡⟨ sym (cong (c⁻¹ ⋆_) cx≡y) ⟩
        c⁻¹ ⋆ (c ⋆ x)    ≡⟨ sym (⋆Assoc _ _ _) ⟩
        (c⁻¹ · c) ⋆ x    ≡⟨ cong (_⋆ x) (·-linv c) ⟩
        1r ⋆ x           ≡⟨ ⋆IdL _  ⟩
        x                ∎ )
      where
        instance _ = c∈kˣ
        c⁻¹ = c ⁻¹

    transitive isEquivRel-lin-eq x y z (c , c∈kˣ , cx≡y) (d , d∈kˣ , dy≡z) =
      d · c ,
      RˣMultClosed d c ,
      ( ((d · c) ⋆ x)    ≡⟨ ⋆Assoc _ _ _ ⟩
        (d ⋆ (c ⋆ x))    ≡⟨ cong (_ ⋆_) cx≡y ⟩
        (d ⋆ y)          ≡⟨ dy≡z ⟩
        z                ∎ )
      where
        instance
          _ = c∈kˣ
          _ = d∈kˣ

    -- Note: linear-equivalent is not prop-valued as a relation on 𝔸ⁿ⁺¹
    -- but it is if we restrict to 𝔸ⁿ⁺¹-0 and assume k to be local and SQC.
    -- It doesn't seem like we need this for now.

  ℙ : Type _
  ℙ = 𝔸ⁿ⁺¹-0 / (pulledbackRel fst linear-equivalent)

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
                  (⇒∶ step2 (fst x) (fst y) x~y
                   ⇐∶ step2 (fst y) (fst x) (symmetric _ _ x~y))
        where
          step1 : (u v w : ⟨ k ⟩) → (u ∈ k ˣ) → (v ∈ k ˣ) → u · v ≡ w → w ∈ k ˣ
          step1 u v w u∈kˣ v∈kˣ p = subst (_∈ k ˣ) p (Units.RˣMultClosed k u v)
            where
              instance
                _ = u∈kˣ
                _ = v∈kˣ
          step2 : (x y : _) → linear-equivalent x y → x i ∈ k ˣ → y i ∈ k ˣ
          step2 x y (c , c∈kˣ , cx≡y) xi∈kˣ = step1 c (x i) (y i) c∈kˣ xi∈kˣ (funExt⁻ cx≡y i)
          open BinaryRelation.isEquivRel isEquivRel-lin-eq

    embedded-𝔸ⁿ : Type ℓ
    embedded-𝔸ⁿ = Σ[ x ∈ 𝔸ⁿ⁺¹ ] x i ≡ 1r

    module _
      (k-local : isLocal k)
      where

      ι : embedded-𝔸ⁿ → ℙ
      ι (x , xi≡1) = [ x , (λ x≡0 → 1≢0 (sym xi≡1 ∙ cong (λ x → x i) x≡0)) ]
        where
        open Consequences k k-local

      ι-injective : (x y : embedded-𝔸ⁿ) → ι x ≡ ι y → x ≡ y
      ι-injective (x , xi≡1) (y , yi≡1) ιx≡ιy =
        Σ≡Prop
          (λ _ → k.is-set _ _)
          (PT.rec (𝔸ⁿ⁺¹.is-set _ _) lineq→≡ (Iso.fun (isEquivRel→TruncIso eqRel _ _) ιx≡ιy))
        where
        eqRel = isEquivRelPulledbackRel fst linear-equivalent isEquivRel-lin-eq
        lineq→≡ : linear-equivalent x y → x ≡ y
        lineq→≡ (c , _ , cx≡y) =
          x        ≡⟨ sym (⋆IdL _) ⟩
          1r ⋆ x   ≡⟨ cong (_⋆ _) (sym c≡1) ⟩
          c ⋆ x    ≡⟨ cx≡y ⟩
          y        ∎
          where
          c≡1 : c ≡ 1r
          c≡1 =
            c         ≡⟨ sym (·IdR _) ⟩
            c · 1r    ≡⟨ cong (_ ·_) (sym xi≡1) ⟩
            c · x i   ≡⟨ funExt⁻ cx≡y i ⟩
            y i       ≡⟨ yi≡1 ⟩
            1r        ∎

      ι-embedding : isEmbedding ι
      ι-embedding = injEmbedding squash/ (ι-injective _ _)

      imι⊆U : (x : embedded-𝔸ⁿ) → fst (fst (U (ι x)))
      imι⊆U (x , xi≡1) = subst (_∈ (k ˣ)) (sym xi≡1) RˣContainsOne

      U⊆imι : (p : ℙ) → fst (fst (U p)) → fiber ι p
      U⊆imι =
        elimProp
          (λ p → isProp→ (injective→hasPropFibers squash/ (ι-injective _ _) p))
          λ{ (x , _) xi∈kˣ@(c , xic≡1) →
              (c ⋆ x , ·Comm c (x i) ∙ xic≡1) ,
              eq/ _ _ ( x i , xi∈kˣ ,
                ( x i ⋆ (c ⋆ x)    ≡⟨ sym (⋆Assoc _ _ _) ⟩
                  (x i · c) ⋆ x    ≡⟨ cong (_⋆ _) xic≡1 ⟩
                  1r ⋆ x           ≡⟨ ⋆IdL _ ⟩
                  x                ∎ ) )}

    embedded-𝔸ⁿ-is-𝔸ⁿ : embedded-𝔸ⁿ ≡ 𝔸 k n
    embedded-𝔸ⁿ-is-𝔸ⁿ =
      embedded-𝔸ⁿ                               ≡⟨⟩
      ((Fin (n + 1) , i) →∙ (⟨ k ⟩ , 1r))       ≡⟨ cong (_→∙ _) transformDomain ⟩
      (Maybe∙ (Fin n) →∙ (⟨ k ⟩ , 1r))          ≡⟨ isoToPath (freelyPointedIso _ _) ⟩
      FinVec ⟨ k ⟩ n                            ≡⟨ sym (std-affine-space-as-product k n) ⟩
      𝔸 k n                                     ∎
      where
      transformDomain : (Fin (n + 1) , i) ≡ Maybe∙ (Fin n)
      transformDomain =
        (Fin (n + 1) , i)        ≡⟨ (pointed-sip _ _ (pathToEquiv (cong Fin (+-comm n 1)) , refl)) ⟩
        (Fin (ℕ.suc n) , _)      ≡⟨ (isHomogeneousDiscrete discreteFin zero) ⟩
        (Fin (ℕ.suc n) , zero)   ≡⟨ finSuc≡Maybe∙ ⟩
        Maybe∙ (Fin n)           ∎

  covering : isLocal k → sqc-over-itself k → (p : ℙ) → ∃[ i ∈ Fin (n + 1) ] ⟨ fst (U i p) ⟩
  covering k-local k-sqc =
    SQ.elimProp
      (λ _ → isPropPropTrunc)
      λ x → generalized-field-property k k-local k-sqc (fst x) (snd x)
```
