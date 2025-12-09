{-# OPTIONS --without-K --safe #-}

-- Monoid with respect to ⊗.
module Container.Algebra.TensorMonoid where

open import Level

import Function as F
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product as Prod
  using (Σ; _×_; _,_; proj₁; proj₂)
  renaming (_,′_ to pair)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Tensor as T
  using (Id; _⊗_; map₁; map₂)

module _ {s p} {C : Container s p} where
  -- Less polymorphic operations
  unitLeft : Id ⊗ C ⇒ C
  unitLeft = T.unitLeft

  unitRight : C ⊗ Id ⇒ C
  unitRight = T.unitRight

  assocʳ : (C ⊗ C) ⊗ C ⇒ C ⊗ (C ⊗ C)
  assocʳ = T.assocʳ

record RawMonoid {s p} (C : Container s p) : Set (s ⊔ p) where
  field
    unit : Id ⇒ C
    mult : C ⊗ C ⇒ C

record IsMonoid {s p} (C : Container s p) (raw : RawMonoid C) : Set (s ⊔ p) where
  open RawMonoid raw

  field
    left-unit : mult ∘ map₁ unit ≈ unitLeft
    right-unit : mult ∘ map₂ unit ≈ unitRight
    assoc : mult ∘ map₁ mult ≈ mult ∘ map₂ mult ∘ assocʳ

record Monoid {s p} (Con : Container s p) : Set (s ⊔ p) where
  field
    rawMonoid : RawMonoid Con
    isMonoid : IsMonoid Con rawMonoid
  
  open RawMonoid rawMonoid public
  open IsMonoid isMonoid public
