{-# OPTIONS --without-K --safe #-}

-- A Monad is a monoid with respect to composition
-- of containers.
module Container.Algebra.Monad where

open import Level

open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

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
  unitLeft : Comp Id C ⇒ C
  unitLeft = Compose.unitLeft

  ununitLeft : C ⇒ Comp Id C
  ununitLeft = Compose.ununitLeft

  unitRight : Comp C Id ⇒ C
  unitRight = Compose.unitRight

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

-- Monad implies TensorMonoid

module _ {C : Container s p} (raw : RawMonad C) where
  open import Container.Combinator.Tensor.Properties using (⊗⇒Comp)
  open import Container.Algebra.TensorMonoid using (RawMonoid)

  open RawMonad raw

  toRawMonoid : RawMonoid C
  toRawMonoid = record {
      unit = unit;
      mult = join ∘ ⊗⇒Comp C C 
    }

module _ {C : Container s p} {raw : RawMonad C} (law : IsMonad C raw) where
  open import Container.Combinator.Tensor as ⊗
    using (_⊗_)
  open import Container.Combinator.Tensor.Properties as ⊗Prop
    using (⊗⇒Comp)
  open import Container.Algebra.TensorMonoid as TM
    using (RawMonoid; IsMonoid)
  import Container.Combinator.Compose.Properties as CompProp

  open RawMonad raw

  rawMonoid : RawMonoid C
  rawMonoid = toRawMonoid raw

  module M = RawMonoid rawMonoid
  open IsMonad law
  
  open IsEquivalence {{...}}

  private
    left-unit-⊗ : M.mult ∘ ⊗.map₁ M.unit ≈ TM.unitLeft
    left-unit-⊗ =
      begin
        M.mult ∘ ⊗.map₁ M.unit
      ≈⟨ refl ⟩
        join ∘ ⊗⇒Comp C C ∘ ⊗.map₁ unit
      ≈⟨ ∘-cong₂ join (⊗Prop.⊗⇒Comp-nat₁ unit) ⟩
        join ∘ map₁ unit ∘ ⊗⇒Comp Id C
      ≈⟨ refl ⟩
        (join ∘ map₁ unit ∘ ununitLeft) ∘ (unitLeft ∘ ⊗⇒Comp Id C)
      ≈⟨ ∘-cong₁ left-unit (unitLeft ∘ ⊗⇒Comp Id C) ⟩
        unitLeft ∘ ⊗⇒Comp Id C
      ≈⟨ refl ⟩
        TM.unitLeft
      ∎
      where open Reasoning (≈-setoid {C₁ = Id {s} {p} ⊗ C} {C₂ = C})
    
    right-unit-⊗ : M.mult ∘ ⊗.map₂ M.unit ≈ TM.unitRight
    right-unit-⊗ =
      begin
        M.mult ∘ ⊗.map₂ M.unit
      ≈⟨ refl ⟩
        join ∘ ⊗⇒Comp C C ∘ ⊗.map₂ unit
      ≈⟨ ∘-cong₂ join (⊗Prop.⊗⇒Comp-nat₂ unit) ⟩
        join ∘ map₂ unit ∘ ⊗⇒Comp C Id
      ≈⟨ refl ⟩
        (join ∘ map₂ unit ∘ ununitRight) ∘ (unitRight ∘ ⊗⇒Comp C Id)
      ≈⟨ ∘-cong₁ right-unit (unitRight ∘ ⊗⇒Comp C Id) ⟩
        unitRight ∘ ⊗⇒Comp C Id
      ≈⟨ refl ⟩
        TM.unitRight
      ∎
      where open Reasoning (≈-setoid {C₁ = C ⊗ Id {s} {p}} {C₂ = C})
    
    assoc-⊗ : M.mult ∘ ⊗.map₁ M.mult ≈ M.mult ∘ ⊗.map₂ M.mult ∘ TM.assocʳ
    assoc-⊗ =
      begin
        M.mult ∘ ⊗.map₁ M.mult
      ≈⟨ refl ⟩
        join ∘ ⊗⇒Comp C C ∘ ⊗.map₁ M.mult
      ≈⟨ ∘-cong₂ join (⊗Prop.⊗⇒Comp-nat₁ M.mult) ⟩
        join ∘ map₁ M.mult ∘ ⊗⇒Comp (C ⊗ C) C
      ≈⟨ refl ⟩
        join ∘ map₁ (join ∘ ⊗⇒Comp C C) ∘ ⊗⇒Comp (C ⊗ C) C
      ≈⟨ ∘-cong₁ (∘-cong₂ join aux1) (⊗⇒Comp (C ⊗ C) C) ⟩
        join ∘ map₁ join ∘ map₁ (⊗⇒Comp C C) ∘ ⊗⇒Comp (C ⊗ C) C
      ≈⟨ ∘-cong₁ assoc (map₁ (⊗⇒Comp C C) ∘ ⊗⇒Comp (C ⊗ C) C) ⟩ 
        join ∘ map₂ join ∘ assocʳ ∘ map₁ (⊗⇒Comp C C) ∘ ⊗⇒Comp (C ⊗ C) C
      ≈⟨ ∘-cong₂ (join ∘ map₂ join) aux2 ⟩
        join ∘ map₂ join ∘ map₂ (⊗⇒Comp C C) ∘ ⊗⇒Comp C (C ⊗ C) ∘ ⊗.assocʳ
      ≈⟨ refl ⟩
        join ∘ map₂ (join ∘ ⊗⇒Comp C C) ∘ ⊗⇒Comp C (C ⊗ C) ∘ ⊗.assocʳ
      ≈⟨ refl ⟩
        join ∘ ⊗⇒Comp C C ∘ ⊗.map₂ (join ∘ ⊗⇒Comp C C) ∘ ⊗.assocʳ
      ≈⟨ refl ⟩
        M.mult ∘ ⊗.map₂ M.mult ∘ TM.assocʳ
      ∎
      where
        open Reasoning (≈-setoid {C₁ = (C ⊗ C) ⊗ C} {C₂ = C})

        -- CompProp.functorial₁
        aux1 : map₁ (join ∘ ⊗⇒Comp C C) ≈ map₁ join ∘ map₁ (⊗⇒Comp C C)
        aux1 = refl

        -- `⊗⇒Comp` preserves associators (`assocʳ`, `⊗.assocʳ`)
        aux2 :
          assocʳ ∘ map₁ (⊗⇒Comp C C) ∘ ⊗⇒Comp (C ⊗ C) C
            ≈ map₂ (⊗⇒Comp C C) ∘ ⊗⇒Comp C (C ⊗ C) ∘ ⊗.assocʳ
        aux2 = refl

  toIsMonoid : IsMonoid C rawMonoid
  toIsMonoid = record {
      left-unit = left-unit-⊗;
      right-unit = right-unit-⊗;
      assoc = assoc-⊗
    }