{-# OPTIONS --without-K --safe #-}

-- Monoid morphism w.r.t. ⊗
module Container.Algebra.TensorMonoid.Morphism where

open import Level

import Function as F
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product as Prod
  using (Σ; _×_; _,_; proj₁; proj₂)
  renaming (_,′_ to pair)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Data.Container.Core

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_; mk⇔)
open import Container.Combinator.Tensor as T
  using (Id; _⊗_; map₁; map₂)

open import Container.Algebra.TensorMonoid

record IsMorphism
  {c c' d d'} {C : Container c c'} {D : Container d d'}
  {{MC : Monoid C}} {{MD : Monoid D}} (α : C ⇒ D)
    : Set (c ⊔ c' ⊔ d ⊔ d') where

  open Monoid {{...}}

  field
    preserve-unit : α ∘ unit ≈ unit
    preserve-mult : α ∘ mult ≈ mult ∘ map₁ α ∘ map₂ α

module _ {c c' d d'} {C : Container c c'} {D : Container d d'} {{MC : Monoid C}} {{MD : Monoid D}} where
  open Monoid {{...}}
  open import Container.Combinator.Tensor.Properties

  IsIsomorphism : (C ⇔ D) → Set _
  IsIsomorphism iso = IsMorphism (iso ._⇔_.to) × IsMorphism (iso ._⇔_.from)

  inverseIsMorphism : 
      (iso : C ⇔ D)
    → IsMorphism (iso ._⇔_.to)
    → IsMorphism (iso ._⇔_.from)
  inverseIsMorphism (mk⇔ f g fg-id gf-id) isMorphism = record {
      preserve-unit = g-preserve-unit ;
      preserve-mult = g-preserve-mult
    }
    where
      open IsEquivalence {{...}}
      open IsMorphism isMorphism

      g-preserve-unit : g ∘ unit ≈ unit
      g-preserve-unit = begin
          g ∘ unit
        ≈⟨ ∘-cong₂ g preserve-unit ⟨
          g ∘ f ∘ unit
        ≈⟨ ∘-cong₁ gf-id unit ⟩
          id C ∘ unit
        ∎
        where open Reasoning (≈-setoid {C₁ = Id} {C₂ = C})
      g-preserve-mult : g ∘ mult ≈ mult ∘ map₁ g ∘ map₂ g
      g-preserve-mult = begin
          g ∘ mult
        ≈⟨ ∘-cong₂ (g ∘ mult) (map₁-cong fg-id) ⟨
          g ∘ mult ∘ map₁ (f ∘ g)
        ≈⟨ ∘-cong₂ (g ∘ mult ∘ map₁ (f ∘ g)) (map₂-cong fg-id) ⟨
          g ∘ mult ∘ map₁ (f ∘ g) ∘ map₂ (f ∘ g)
        ≈⟨ refl ⟩
          g ∘ mult ∘ map₁ f ∘ map₂ f ∘ map₁ g ∘ map₂ g
        ≈⟨ ∘-cong₁ (∘-cong₂ g preserve-mult) (map₁ g ∘ map₂ g) ⟨
          g ∘ f ∘ mult ∘ map₁ g ∘ map₂ g
        ≈⟨ ∘-cong₁ gf-id (mult ∘ map₁ g ∘ map₂ g) ⟩
          mult ∘ map₁ g ∘ map₂ g
        ∎
        where open Reasoning (≈-setoid {C₁ = D ⊗ D} {C₂ = C})

module _ {c c' d d'} {C : Container c c'} {D : Container d d'} (iso : C ⇔ D) where
  open _⇔_ iso renaming (to to f; from to g; to-from to fg-id; from-to to gf-id)

  open import Container.Combinator.Tensor.Properties
  open IsEquivalence {{...}}

  transferRawMonoid : RawMonoid C → RawMonoid D
  transferRawMonoid raw = record { unit = unit'; mult = mult' }
    where
      open RawMonoid raw
      unit' : Id ⇒ D
      unit' = f ∘ unit

      mult' : D ⊗ D ⇒ D
      mult' = f ∘ mult ∘ map₁ g ∘ map₂ g

  transferIsMonoid : {raw : RawMonoid C} → IsMonoid C raw → IsMonoid D (transferRawMonoid raw)
  transferIsMonoid {raw} law = record {
      left-unit = left-unit';
      right-unit = right-unit';
      assoc = assoc'
    }
    where
      open RawMonoid raw
      open IsMonoid law

      raw' : RawMonoid D
      raw' = transferRawMonoid raw
      open RawMonoid raw' renaming (unit to unit'; mult to mult')

      g-unit' : g ∘ unit' ≈ unit
      g-unit' = ∘-cong₁ gf-id unit

      g-mult' : g ∘ mult' ≈ mult ∘ map₁ g ∘ map₂ g
      g-mult' = ∘-cong₁ gf-id (mult ∘ map₁ g ∘ map₂ g)

      left-unit' : mult' ∘ map₁ unit' ≈ unitLeft
      left-unit' = begin
          mult' ∘ map₁ unit'
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₁ g ∘ map₂ g ∘ map₁ unit'
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₁ (g ∘ unit') ∘ map₂ g
        ≈⟨ ∘-cong-mid (f ∘ mult) (map₁-cong g-unit') (map₂ g) ⟩
          f ∘ mult ∘ map₁ unit ∘ map₂ g
        ≈⟨ ∘-cong-mid f left-unit (map₂ g) ⟩
          f ∘ unitLeft ∘ map₂ g
        ≈⟨ refl ⟩
          f ∘ g ∘ unitLeft
        ≈⟨ ∘-cong₁ fg-id unitLeft ⟩
          unitLeft
        ∎
        where open Reasoning ≈-setoid
      
      right-unit' : mult' ∘ map₂ unit' ≈ unitRight
      right-unit' = begin
          mult' ∘ map₂ unit'
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₁ g ∘ map₂ g ∘ map₂ unit'
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₁ g ∘ map₂ (g ∘ unit')
        ≈⟨ ∘-cong₂ (f ∘ mult ∘ map₁ g) (map₂-cong g-unit') ⟩
          f ∘ mult ∘ map₁ g ∘ map₂ unit
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₂ unit ∘ map₁ g
        ≈⟨ ∘-cong-mid f right-unit (map₁ g) ⟩
          f ∘ unitRight ∘ map₁ g
        ≈⟨ refl ⟩
          f ∘ g ∘ unitRight
        ≈⟨ ∘-cong₁ fg-id unitRight ⟩
          unitRight
        ∎
        where open Reasoning ≈-setoid

      assoc' : mult' ∘ map₁ mult' ≈ mult' ∘ map₂ mult' ∘ assocʳ
      assoc' = begin
          mult' ∘ map₁ mult'
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₁ g ∘ map₂ g ∘ map₁ mult'
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₁ (g ∘ mult') ∘ map₂ g
        ≈⟨ ∘-cong-mid (f ∘ mult) (map₁-cong g-mult') (map₂ g) ⟩
          f ∘ mult ∘ map₁ (mult ∘ map₁ g ∘ map₂ g) ∘ map₂ g
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₁ mult ∘ map₁ (map₁ g ∘ map₂ g) ∘ map₂ g
        ≈⟨ ∘-cong-mid f assoc (map₁ (map₁ g ∘ map₂ g) ∘ map₂ g) ⟩
          f ∘ mult ∘ map₂ mult ∘ assocʳ ∘ map₁ (map₁ g ∘ map₂ g) ∘ map₂ g
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₂ mult ∘ map₁ g ∘ map₂ (map₁ g ∘ map₂ g) ∘ assocʳ
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₂ (mult ∘ map₁ g ∘ map₂ g) ∘ map₁ g ∘ assocʳ
        ≈⟨ ∘-cong-mid (f ∘ mult) (map₂-cong g-mult') (map₁ g ∘ assocʳ) ⟨
          f ∘ mult ∘ map₂ (g ∘ mult') ∘ map₁ g ∘ assocʳ
        ≈⟨ refl ⟩
          f ∘ mult ∘ map₂ g ∘ map₁ g ∘ map₂ mult' ∘ assocʳ
        ≈⟨ refl ⟩
          mult' ∘ map₂ mult' ∘ assocʳ
        ∎
        where open Reasoning ≈-setoid

  module transfer (MC : Monoid C) where
    open Monoid {{...}}

    instance
      _ : Monoid C
      _ = MC

      transferMonoid : Monoid D
      transferMonoid = record { isMonoid = law' }
        where
          raw' : RawMonoid D
          raw' = transferRawMonoid rawMonoid

          law' : IsMonoid D raw'
          law' = transferIsMonoid isMonoid

    to-morphism : IsMorphism f
    to-morphism = record {
        preserve-unit = refl;
        preserve-mult = begin
            f ∘ mult
          ≈⟨ ∘-cong₂ (f ∘ mult) (map₁-cong gf-id) ⟨
            f ∘ mult ∘ map₁ (g ∘ f)
          ≈⟨ ∘-cong₂ (f ∘ mult ∘ map₁ (g ∘ f)) (map₂-cong gf-id) ⟨
            f ∘ mult ∘ map₁ (g ∘ f) ∘ map₂ (g ∘ f)
          ≈⟨ refl ⟩
            f ∘ mult ∘ map₁ g ∘ map₂ g ∘ map₁ f ∘ map₂ f
          ≈⟨ refl ⟩
            mult ∘ map₁ f ∘ map₂ f
          ∎
      }
      where open Reasoning ≈-setoid
    
    from-morphism : IsMorphism g
    from-morphism = record {
        preserve-unit = ∘-cong₁ gf-id unit;
        preserve-mult = ∘-cong₁ gf-id (mult ∘ map₁ g ∘ map₂ g)
      }
    
    isomorphism : IsIsomorphism iso
    isomorphism = to-morphism , from-morphism
  
  open transfer using (transferMonoid) public