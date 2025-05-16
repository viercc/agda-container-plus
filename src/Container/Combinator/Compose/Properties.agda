{-# OPTIONS --without-K --safe #-}

  -- Properties of container compositions (Comp = CC._∘_)
module Container.Combinator.Compose.Properties where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

open import Data.Container.Core renaming (map to map⟦⟧)
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Morphism as CM using (id; _∘_)   -- Container Morphism
import Data.Container.Combinator as CC -- Container Combinator
import Data.Container.Relation.Binary.Equality.Setoid as CEq -- Container equality

open import Container.Morphism.Equality using (_≈_; mk≈)
open import Container.Morphism.Iso

open import Container.Combinator.Compose
open import Container.Combinator.Monoidal

private
  variable
    c c' d d' e e' f f' : Level

module _ {c c' d d' : Level} where
  functorial₁ : {D : Container d d'} → Functorial (λ (C : Container c c') → Comp C D) map₁
  functorial₁ {D = D} = record {
      map-id = λ {C} → mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl);
      map-∘ = λ {C₁ C₂ C₃} _ _ → mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
    }

  functorial₂ : {C : Container c c'} → Functorial (λ (D : Container d d') → Comp C D) map₂
  functorial₂ {C = C} = record {
      map-id = λ {D} → mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl);
      map-∘ = λ {D₁ D₂ D₃} _ _ → mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
    }

  bifunctorial : Bifunctorial (λ (C : Container c c') (D : Container d d') → Comp C D) map₁ map₂
  bifunctorial = record {
      functorial₁ = functorial₁;
      functorial₂ = functorial₂;
      map₁-map₂ = λ {C₁ C₂ D₁ D₂} _ _ → mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
    }

open _⇔_
open ◇-util

-- Associativity

module _ {c c' d d' e e'}
  {C : Container c c'}
  {D : Container d d'}
  {E : Container e e'} where
  assoc⇔ : Comp (Comp C D) E ⇔ Comp C (Comp D E)
  assoc⇔ = mk⇔ assocʳ assocˡ iso₁ iso₂
    where
      iso₁ : assocʳ ∘ assocˡ ≈ id (Comp C (Comp D E))
      iso₁ = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)

      iso₂ : assocˡ ∘ assocʳ ≈ id (Comp (Comp C D) E)
      iso₂ = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)

module _ {c c' d d' e e'}
  {C₁ C₂ : Container c c'}
  {D₁ D₂ : Container d d'}
  {E₁ E₂ : Container e e'} where
  
  assoc-nat : ∀ (α : C₁ ⇒ C₂) (β : D₁ ⇒ D₂) (γ : E₁ ⇒ E₂)
        → bimap α (bimap β γ) ∘ assocʳ ≈ assocʳ ∘ bimap (bimap α β) γ
  assoc-nat _ _ _ = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)

-- TODO:
-- 
-- semigroupal : {c : Level} → Semigroupal {c = c} {c' = c} Comp map₁ map₂ assoc⇔
-- semigroupal {c} = _

-- Units
module _ {c c'} {C : Container c c'} where
  private
    Id' : Container c c'
    Id' = CC.id
  
  unitLeft⇔ : Comp Id' C ⇔ C
  unitLeft⇔ = record {
      to = unitLeft; from = ununitLeft;
      to-from = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl);
      from-to = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
    }

  unitRight⇔ : Comp C Id' ⇔ C
  unitRight⇔ = record {
      to = unitRight; from = ununitRight;
      to-from = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl);
      from-to = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)
    }

-- TODO:
-- 
-- monoidal : {c : Level} → Monoidal {c = c} {c' = c} Comp CC.id map₁ map₂ assoc⇔ unitLeft⇔ unitRight⇔
-- monoidal {c} = _