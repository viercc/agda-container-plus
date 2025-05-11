{-# OPTIONS --without-K --safe #-}

module Container.Combinator.Properties where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using ()
    renaming (_≡_ to infix 3 _≡_)

open import Data.Container.Core renaming (map to map⟦⟧)
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

import Data.Container.Morphism as CM   -- Container Morphism
import Data.Container.Combinator as CC -- Container Combinator
import Data.Container.Relation.Binary.Equality.Setoid as CEq -- Container equality

open CC using () renaming (_∘_ to Comp)

open import Container.Morphism.Equality using (_≈_; mk≈)
open import Container.Morphism.Iso

private
  variable
    c c' d d' e e' f f' : Level

module _ (H : Container c c' → Container d d') where
  Map : Set (suc (c ⊔ c') ⊔ d ⊔ d')
  Map = ∀ {C₁ C₂ : Container c c'} → (C₁ ⇒ C₂) → (H C₁ ⇒ H C₂)

  record Functorial (map : Map) : Set (suc (c ⊔ c') ⊔ d ⊔ d') where
    constructor mkFunctorial
    field
      map-id : ∀ {C₁ : Container c c'} → map (CM.id C₁) ≈ CM.id (H C₁)
      
      map-∘ : ∀ {C₁ C₂ C₃ : Container c c'}
        → (α : C₂ ⇒ C₃) → (β : C₁ ⇒ C₂) → map (α CM.∘ β) ≈ map α CM.∘ map β  

module _ (H : Container c c' → Container d d' → Container e e') where
  Map₁ : Set (suc (c ⊔ c' ⊔ d ⊔ d') ⊔ e ⊔ e')
  Map₁ = ∀ {C₁ C₂ : Container c c'} {D : Container d d'} → (C₁ ⇒ C₂) → (H C₁ D ⇒ H C₂ D)

  Map₂ : Set (suc (c ⊔ c' ⊔ d ⊔ d') ⊔ e ⊔ e')
  Map₂ = ∀ {C : Container c c'} {D₁ D₂ : Container d d'} → (D₁ ⇒ D₂) → (H C D₁ ⇒ H C D₂)

  record Bifunctorial (map₁ : Map₁) (map₂ : Map₂) : Set (suc (c ⊔ c' ⊔ d ⊔ d') ⊔ e ⊔ e') where
    constructor mkFunctorial
    field
      functorial₁ : ∀ {D} → Functorial (λ C → H C D) map₁
      functorial₂ : ∀ {C} → Functorial (H C) map₂
      map₁-map₂ : ∀ {C₁ C₂ D₁ D₂}
        → (α : C₁ ⇒ C₂) → (β : D₁ ⇒ D₂) → map₁ α CM.∘ map₂ β ≈ map₂ β CM.∘ map₁ α  

module ∘-Properties where

  -- Identity container with level specified to zero
  Id : Container Level.zero Level.zero
  Id = CC.id

  -- Properties of container compositions (Comp = CC._∘_)

  -- Comp is bifunctor (Container × Container) → Container
  map₁ : ∀ {C : Container c c'} {D : Container d d'} {E : Container e e'}
    → (C ⇒ D) → (Comp C E ⇒ Comp D E)
  map₁ α .shape    = ⟪ α ⟫
  map₁ α .position = C◇.map₁ α
  
  map₂ : ∀ {C : Container c c'} {E : Container e e'} {F : Container f f'}
    → (E ⇒ F) → (Comp C E ⇒ Comp C F)
  map₂ α .shape    = map⟦⟧ (shape α)
  map₂ α .position { s = s } (mk◇ pp) =
    mk◇ (Prod.map₂ (λ {pc} → position α {proj₂ s pc}) pp)
  
  open Container.Morphism.Equality.≈-correctness
    using ()
    renaming (≡⟪⟫'→≈ to with≡)

  functorial₁ : {D : Container d d'} → Functorial (λ (C : Container c c') → Comp C D) map₁
  functorial₁ {D = D} = record {
      map-id = λ {C} → with≡ (Comp C D) (Comp C D) (λ _ → P.refl);
      map-∘ = λ {C₁ C₂ C₃} _ _ → with≡ (Comp C₁ D) (Comp C₃ D) (λ _ → P.refl)
    }

  functorial₂ : {C : Container c c'} → Functorial (λ (D : Container d d') → Comp C D) map₂
  functorial₂ {C = C} = record {
      map-id = λ {D} → with≡ (Comp C D) (Comp C D) (λ _ → P.refl);
      map-∘ = λ {D₁ D₂ D₃} _ _ → with≡ (Comp C D₁) (Comp C D₃) (λ _ → P.refl)
    }
  
  bifunctorial : Bifunctorial (λ (C : Container c c') (D : Container d d') → Comp C D) map₁ map₂
  bifunctorial = record {
      functorial₁ = functorial₁;
      functorial₂ = functorial₂;
      map₁-map₂ = λ {C₁ C₂ D₁ D₂} _ _ → with≡ (Comp C₁ D₁) (Comp C₂ D₂) (λ _ → P.refl)
    }
  
  -- Comp is monoidal

  module _ where
    open _⇔_

    leftId : ∀ {C : Container c c'}
      → C ⇔ Comp Id C
    leftId {C = C} .to   = CC.to-id ▷ λ (mk◇ (_ , p)) → p
    leftId {C = C} .from = CC.from-id ▷ λ p → mk◇ (tt , p)
    leftId {C = C} .to-from = with≡ (Comp Id C) (Comp Id C) (λ _ → P.refl)
    leftId {C = C} .from-to = with≡ C C (λ _ → P.refl)

    rightId : ∀ {C : Container c c'}
      → C ⇔ Comp C Id
    rightId {C = C} .to   = (λ s → s , F.const tt) ▷ λ (mk◇ (p , _)) → p
    rightId {C = C} .from = proj₁ ▷ λ p → mk◇ (p , tt)
    rightId {C = C} .to-from = with≡ (Comp C Id) (Comp C Id) (λ _ → P.refl)
    rightId {C = C} .from-to = with≡ C C (λ _ → P.refl)

    assoc : ∀ {C : Container c c'} {D : Container d d'} {E : Container e e'}
      → Comp (Comp C D) E ⇔ Comp C (Comp D E)
    assoc {C = C} {D = D} {E = E} = mk⇔ assoc⇒ assoc⇐ iso₁ iso₂
      where
        to-shape : ⟦ Comp C D ⟧ (Shape E) → ⟦ C ⟧ (⟦ D ⟧ (Shape E))
        to-shape = CC.from-∘ C D

        to-pos : { sCDE : ⟦ Comp C D ⟧ (Shape E) }
          → ◇ C (◇ D (Position E)) (to-shape sCDE) 
          → ◇ (Comp C D) (Position E) sCDE
        to-pos {sCDE} (mk◇ (pc , mk◇ (pd , pe))) = mk◇ (mk◇ (pc , pd) , pe)

        from-shape : ⟦ C ⟧ (⟦ D ⟧ (Shape E)) → ⟦ Comp C D ⟧ (Shape E)
        from-shape = CC.to-∘ C D

        from-pos : { sCDE : ⟦ C ⟧ (⟦ D ⟧ (Shape E)) }
          → ◇ (Comp C D) (Position E) (from-shape sCDE)
          → ◇ C (◇ D (Position E)) sCDE
        from-pos {sCDE} (mk◇ (mk◇ (pc , pd) , pe)) = mk◇ (pc , mk◇ (pd , pe))

        assoc⇒ = to-shape ▷ to-pos
        assoc⇐ = from-shape ▷ from-pos

        iso₁ : assoc⇒ CM.∘ assoc⇐ ≈ CM.id (Comp C (Comp D E))
        iso₁ = with≡ _ _ (λ _ → P.refl)

        iso₂ : assoc⇐ CM.∘ assoc⇒ ≈ CM.id (Comp (Comp C D) E)
        iso₂ = with≡ _ _ (λ _ → P.refl)