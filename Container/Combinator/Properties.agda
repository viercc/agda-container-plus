{-# OPTIONS --without-K --safe #-}

module Container.Combinator.Properties where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)

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

open CC using () renaming (id to Id; _∘_ to Comp)

module ∘-Properties where

  -- Properties of container compositions (Comp = CC._∘_)

  private
    variable
      c c' d d' e e' f f' : Level
  
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
  
  -- We verify the "laws" of bifunctor only up to ⟪_⟫.
  -- This is a slop but actually ok, because
  -- `Data.Container.Morphism.Properties` shows that container morphism
  -- (C ⇒ D) faithfully represents every natural transformation from ⟦ C ⟧ to ⟦ D ⟧
  -- via ⟪_⟫.

  map₁-id : ∀ {C : Container c c'} {E : Container e e'}
    → ∀ {x} {X : Set x}
    → (xs : ⟦ Comp C E ⟧ X) → ⟪ map₁ (CM.id C) ⟫ xs ≡ xs
  map₁-id _ = P.refl

  map₁-∘ : ∀ {C : Container c c'} {D : Container d d'} {E : Container e e'} {F : Container f f'}
    → (mCD : C ⇒ D) → (mDE : D ⇒ E)
    → ∀ {x} {X : Set x}
    → (xs : ⟦ Comp C E ⟧ X) → ⟪ map₁ (mDE CM.∘ mCD) ⟫ xs ≡ ⟪ map₁ mDE ⟫ (⟪ map₁ mCD ⟫ xs)
  map₁-∘ _ _ _ = P.refl

  map₂-id : ∀ {C : Container c c'} {E : Container e e'}
    → ∀ {x} {X : Set x}
    → (xs : ⟦ Comp C E ⟧ X) → ⟪ map₂ (CM.id E) ⟫ xs ≡ xs
  map₂-id _ = P.refl

  map₂-∘ : ∀ {C : Container c c'} {D : Container d d'} {E : Container e e'} {F : Container f f'}
    → (mDE : D ⇒ E) → (mEF : E ⇒ F)
    → ∀ {x} {X : Set x}
    → (xs : ⟦ Comp C D ⟧ X) → ⟪ map₂ (mEF CM.∘ mDE) ⟫ xs ≡ ⟪ map₂ mEF ⟫ (⟪ map₂ mDE ⟫ xs)
  map₂-∘ _ _ _ = P.refl

  map₁-map₂ : ∀ {C : Container c c'} {D : Container d d'} {E : Container e e'} {F : Container f f'}
    → (mCD : C ⇒ D) → (mEF : E ⇒ F)
    → ∀ {x} {X : Set x}
    → (xs : ⟦ Comp C E ⟧ X) → ⟪ map₁ mCD CM.∘ map₂ mEF ⟫ xs ≡ ⟪ map₂ mEF CM.∘ map₁ mCD ⟫ xs
  map₁-map₂ _ _ _ = P.refl
