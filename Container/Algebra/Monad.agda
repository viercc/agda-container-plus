{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Monad where

open import Level

open import Data.Container.Core
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Morphism using (id; _∘_)
open import Data.Container.Combinator
  using () renaming (_∘_ to Comp)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Properties
open ∘-Properties using (map₁; map₂)

private
  variable
    s p : Level

-- Common symbols
module _ {C : Container s p} where
  leftId⇒ : C ⇒ Comp Id C
  leftId⇒ = ∘-Properties.leftId ._⇔_.to

  rightId⇒ : C ⇒ Comp C Id
  rightId⇒ = ∘-Properties.rightId ._⇔_.to

  assoc⇒ : Comp (Comp C C) C ⇒ Comp C (Comp C C)
  assoc⇒ = ∘-Properties.assoc ._⇔_.to

record RawMonad (C : Container s p) : Set (s ⊔ p) where
  open Container C renaming (Shape to S; Position to P) public
  
  field
    unit : Id ⇒ C
    join : Comp C C ⇒ C

record IsMonad (C : Container s p) (raw : RawMonad C) : Set (s ⊔ p) where
  open RawMonad raw

  field
    left-unit : join ∘ map₁ unit ∘ leftId⇒ ≈ id C
    right-unit : join ∘ map₂ unit ∘ rightId⇒ ≈ id C
    assoc : join ∘ map₁ join ≈ join ∘ map₂ join ∘ assoc⇒
