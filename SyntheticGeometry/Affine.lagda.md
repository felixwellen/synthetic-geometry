Affine qc-schemes
=================

```agda
{-# OPTIONS --safe #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function

open import Cubical.Functions.Logic
open import Cubical.Functions.Image

open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommAlgebra
open import Cubical.Algebra.CommAlgebra.Instances.Initial
open import Cubical.Algebra.CommAlgebra.Instances.Pointwise
open import Cubical.Algebra.CommAlgebra.FreeCommAlgebra
open import Cubical.Algebra.CommAlgebra.FPAlgebra
open import Cubical.Algebra.CommRing.LocalRing
import Cubical.Algebra.Algebra
open Cubical.Algebra.Algebra.AlgebraHoms

import SyntheticGeometry.SQC

module SyntheticGeometry.Affine
  {ℓ : Level}
  (k : CommRing ℓ)
  (k-local : isLocal k)
  (k-sqc : SyntheticGeometry.SQC.sqc-over-itself k)
  where

open import SyntheticGeometry.Spec k
open import SyntheticGeometry.Open k
open SyntheticGeometry.SQC k

private variable ℓ' : Level

kₐ = initialCAlg k

```

An affine type is a type, that is equivalent to the spectrum of a fp algebra over the base ring k.
We chose this definition over asking for a coupled algebra, because fp is universe independet.

```agda


is-affine : Type ℓ' → hProp _
is-affine X =
  (∃[ A ∈ (CommAlgebra k ℓ) ] isFPAlgebra A × (X ≃ Spec A)) ,
  isPropPropTrunc

```

A coupled space is not neccessarily affine, but it is still the spectrum of an algebra,
which is coupled, i.e. the canonical map A → (Spec A → k) is an equivalence.
That the following definition is equivalent to this statement will be shown later,
we use another canonical map 'to-ev-hom' for the definition:

```agda

to-ev-hom : (X : Type ℓ') → X → Spec (pointwiseAlgebra X kₐ)
to-ev-hom X = evaluationHom X kₐ

is-coupled : Type ℓ' → hProp _
is-coupled X = (isEquiv (to-ev-hom X)) , isPropIsEquiv _

```

We want to see that: (Spec A ≃ Spec B) = (CommAlgebraIso A B) for any fp algebras A and B.
We will show the more general statement for coupled algebras, which will need a couple of steps:

First, there is a canonical morphism from any type to a spectrum,
which has a left inverse, when the type is a spectrum.


```agda

left-inv-to-ev-hom : (A : CommAlgebra k ℓ') → Spec (pointwiseAlgebra (Spec A) kₐ) → Spec A
left-inv-to-ev-hom A = Spec→ {A = A} {B = pointwiseAlgebra (Spec A) kₐ} (canonical-hom A)

is-left-inv-to-ev-hom : (A : CommAlgebra k ℓ') → (α : Spec A) → (left-inv-to-ev-hom A) (to-ev-hom (Spec A) α) ≡ α
is-left-inv-to-ev-hom A α = make-Spec-eq {A = A} refl

```

If the algebra A is coupled, this left inverse will be an equivalence.
Then, as a one-sided inverse of an equivalence, to-ev-hom will also be an equivalence.

```agda

is-equiv-left-inv : (A : CommAlgebra k ℓ') → ⟨ is-coupled-algebra A ⟩ → isEquiv (left-inv-to-ev-hom A)
is-equiv-left-inv A coupled-A = snd (Spec→≃ {A = A} {B = pointwiseAlgebra (Spec A) kₐ} canonical-equiv)
  where
    canonical-equiv : CommAlgebraEquiv A (pointwiseAlgebra (Spec A) kₐ)
    canonical-equiv = (_ , coupled-A) , snd (canonical-hom A)

is-equiv-to-ev-hom : (A : CommAlgebra k ℓ') → ⟨ is-coupled-algebra A ⟩ → isEquiv (to-ev-hom (Spec A))
is-equiv-to-ev-hom A coupled-A = isEquiv→sectionIsEquiv (is-equiv-left-inv A coupled-A) (is-left-inv-to-ev-hom A)
```

This will be used when showing, that Spec is an embedding on coupled algebras, which we will prove
from Spec on coupled algebras being an equivalence onto its image.

```agda

Spec-coupled : Σ[ A ∈ CommAlgebra k ℓ' ] ⟨ is-coupled-algebra A ⟩ → Type _
Spec-coupled (A , coupled-A) = Spec A

Spec-equiv-onto-image : isEquiv (restrictToImage (Spec-coupled {ℓ' = ℓ}))
Spec-equiv-onto-image = isoToIsEquiv SpecIso
  where
    SpecIso : Iso (Σ[ A ∈ CommAlgebra k ℓ ] ⟨ is-coupled-algebra A ⟩) (Image Spec-coupled)
    Iso.fun SpecIso = restrictToImage Spec-coupled
    Iso.inv SpecIso (X , X∈ImSpec) =
      pointwiseAlgebra X kₐ ,
      PT.rec
        (snd (is-coupled-algebra (pointwiseAlgebra X kₐ)))
        (λ ((A , coupled-A) , SpecA≡X)
        → let A≡X→k : A ≡ (pointwiseAlgebra X kₐ)
              A≡X→k =
                A ≡⟨ fst (CommAlgebraPath k A (pointwiseAlgebra (Spec A) kₐ)) ((_ , coupled-A) , snd (canonical-hom A))  ⟩
                pointwiseAlgebra (Spec A) kₐ  ≡⟨ cong (λ u → pointwiseAlgebra u kₐ) SpecA≡X ⟩
                pointwiseAlgebra X kₐ ∎
          in subst (λ u → ⟨ is-coupled-algebra u ⟩) A≡X→k coupled-A)
        X∈ImSpec
    Iso.rightInv SpecIso (X , X∈ImSpec) =
      Σ≡Prop (λ _ → isPropPropTrunc)
             SpecX→k≡X
      where SpecX→k≡X : Spec (pointwiseAlgebra X kₐ) ≡ X
            SpecX→k≡X = {!!}
    Iso.leftInv SpecIso (A , coupled-A) =
      Σ≡Prop (λ B → snd (is-coupled-algebra B))
             (sym (uaCommAlgebra (((to-ev-map A) , coupled-A) , (snd (canonical-hom A)))))

```

Finite affine qc-open covers
----------------------------
The following is used to define qc-schemes:

```agda

is-affine-finite-qc-open-cover : {n : ℕ}
  → (X : Type ℓ') → (U : Fin n → qc-opens-in X)
  → hProp _
is-affine-finite-qc-open-cover {n = n} X U =
  is-finite-qc-open-cover X U
  ⊓ (∀[ i ∶ Fin n ] is-affine (qc-open-as-type (U i)))

```
