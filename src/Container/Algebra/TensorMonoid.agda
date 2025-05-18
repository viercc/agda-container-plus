{-# OPTIONS --without-K --safe #-}

-- Monoid with respect to ⊗.
module Container.Algebra.TensorMonoid where

open import Level

open import Data.Container.Core
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Tensor as T
  using (Id; _⊗_; map₁; map₂)

module _ {s p} {C : Container s p} where
  -- Less polymorphic operations
  ununitLeft : C ⇒ Id ⊗ C
  ununitLeft = T.ununitLeft

  ununitRight : C ⇒ C ⊗ Id
  ununitRight = T.ununitRight

  assocʳ : (C ⊗ C) ⊗ C ⇒ C ⊗ (C ⊗ C)
  assocʳ = T.assocʳ

record RawMonoid {s p} (C : Container s p) : Set (s ⊔ p) where
  field
    unit : Id {s} {p} ⇒ C
    mult : C ⊗ C ⇒ C

record IsMonoid {s p} (C : Container s p) (raw : RawMonoid C) : Set (s ⊔ p) where
  open RawMonoid raw

  field
    left-unit : mult ∘ map₁ unit ∘ ununitLeft ≈ id C
    right-unit : mult ∘ map₂ unit ∘ ununitRight ≈ id C
    assoc : mult ∘ map₁ mult ≈ mult ∘ map₂ mult ∘ assocʳ

record Monoid {s p} (Con : Container s p) : Set (s ⊔ p) where
  field
    rawMonoid : RawMonoid Con
    isMonoid : IsMonoid Con rawMonoid
  
  open RawMonoid rawMonoid public
  open IsMonoid isMonoid public

-- TODO: TensorMonoid ↔ Action
--   (probably I should rename Action to TensorMonoid.Uustalu)