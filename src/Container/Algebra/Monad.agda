{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Monad where

open import Level

open import Data.Container.Core
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Compose as Compose
  using (Id; Comp; map₁; map₂)

private
  variable
    s p : Level

module _ {C : Container s p} where
  -- Less polymorphic operations
  ununitLeft : C ⇒ Comp Id C
  ununitLeft = Compose.ununitLeft

  ununitRight : C ⇒ Comp C Id
  ununitRight = Compose.ununitRight

  assocʳ : Comp (Comp C C) C ⇒ Comp C (Comp C C)
  assocʳ = Compose.assocʳ

record RawMonad {s p} (C : Container s p) : Set (s ⊔ p) where
  open Container C renaming (Shape to S; Position to P) public
  
  field
    unit : Id {s} {p} ⇒ C
    join : Comp C C ⇒ C

record IsMonad (C : Container s p) (raw : RawMonad C) : Set (s ⊔ p) where
  open RawMonad raw

  field
    left-unit : join ∘ map₁ unit ∘ ununitLeft ≈ id C
    right-unit : join ∘ map₂ unit ∘ ununitRight ≈ id C
    assoc : join ∘ map₁ join ≈ join ∘ map₂ join ∘ assocʳ
