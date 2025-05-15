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

open CC using () renaming (id to Id; _∘_ to Comp) public

open import Container.Morphism.Equality using (_≈_; mk≈)
open import Container.Morphism.Iso

open import Container.Combinator.Monoidal

private
  variable
    c c' d d' e e' f f' : Level

module ◇-util where
  -- proof utility
  module _ {C : Container c c'} where
    open Container C renaming (Shape to S; Position to P)
    
    ◇-dcong : ∀ {x ℓ} {X : Set x} (Q : X → Set ℓ) {cx : ⟦ C ⟧ X}
      → {p₁ p₂ : P (proj₁ cx)} (eq-p : p₁ ≡ p₂)
      → {q₁ : Q (proj₂ cx p₁)} {q₂ : Q (proj₂ cx p₂)}
      → (eq-q : ≡.subst (λ p → Q (proj₂ cx p)) eq-p q₁ ≡ q₂)
      → mk◇ {P = Q} {cx = cx} (p₁ , q₁) ≡ mk◇ (p₂ , q₂)
    ◇-dcong Q eq-p eq-q =
      ≡.dcong₂ (λ r₁ r₂ → mk◇ (r₁ , r₂)) eq-p eq-q
    
    curry◇ : ∀ {x} {X : Set x} {cx : ⟦ C ⟧ X} {ℓ} {Q : X → Set ℓ} {y} {Y : Set y}
      → (◇ C Q cx → Y)
      → ((p : P (proj₁ cx)) → Q (proj₂ cx p) → Y)
    curry◇ k p q = k (mk◇ (p , q))

    uncurry◇ : ∀ {x} {X : Set x} {s : S} {v : P s → X} {ℓ} {Q : X → Set ℓ} {y} {Y : Set y}
      → ((p : P s) → Q (v p) → Y)
      → (◇ C Q (s , v) → Y)
    uncurry◇ w (mk◇ (p , q)) = w p q
  
  module _ {C : Container c c'} {D : Container d d'} where
    ◇-assocˡ : ∀ {x ℓ} {X : Set x} {Q : X → Set ℓ}
      → { cx : ⟦ Comp C D ⟧ X }
      → ◇ C (◇ D Q) (CC.from-∘ C D cx) 
      → ◇ (Comp C D) Q cx
    ◇-assocˡ (mk◇ (p₁ , mk◇ (p₂ , q))) = mk◇ (mk◇ (p₁ , p₂) , q)

    ◇-assocʳ : ∀ {x ℓ} {X : Set x} {Q : X → Set ℓ}
      → { cdx : ⟦ C ⟧ (⟦ D ⟧ X) }
      → ◇ (Comp C D) Q (CC.to-∘ C D cdx)
      → ◇ C (◇ D Q) cdx
    ◇-assocʳ (mk◇ (mk◇ (p₁ , p₂) , q)) = mk◇ (p₁ , mk◇ (p₂ , q))

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

module _ {c c' d d' : Level} where
  functorial₁ : {D : Container d d'} → Functorial (λ (C : Container c c') → Comp C D) map₁
  functorial₁ {D = D} = record {
      map-id = λ {C} → with≡ (Comp C D) (Comp C D) (λ _ → ≡.refl);
      map-∘ = λ {C₁ C₂ C₃} _ _ → with≡ (Comp C₁ D) (Comp C₃ D) (λ _ → ≡.refl)
    }

  functorial₂ : {C : Container c c'} → Functorial (λ (D : Container d d') → Comp C D) map₂
  functorial₂ {C = C} = record {
      map-id = λ {D} → with≡ (Comp C D) (Comp C D) (λ _ → ≡.refl);
      map-∘ = λ {D₁ D₂ D₃} _ _ → with≡ (Comp C D₁) (Comp C D₃) (λ _ → ≡.refl)
    }

  bifunctorial : Bifunctorial (λ (C : Container c c') (D : Container d d') → Comp C D) map₁ map₂
  bifunctorial = record {
      functorial₁ = functorial₁;
      functorial₂ = functorial₂;
      map₁-map₂ = λ {C₁ C₂ D₁ D₂} _ _ → with≡ (Comp C₁ D₁) (Comp C₂ D₂) (λ _ → ≡.refl)
    }
  
  bimap : ∀ {C₁ C₂ : Container c c'} {D₁ D₂ : Container d d'}
    → (C₁ ⇒ C₂) → (D₁ ⇒ D₂) → Comp C₁ D₁ ⇒ Comp C₂ D₂
  bimap = Bifunctorial.bimap bifunctorial

open _⇔_
open ◇-util

-- Associativity

module _ {c c' d d' e e'}
  {C : Container c c'}
  {D : Container d d'}
  {E : Container e e'} where
  assocʳ : Comp (Comp C D) E ⇒ Comp C (Comp D E)
  assocʳ = CC.from-∘ C D ▷ ◇-assocˡ {C = C} {D = D} {Q = Position E}
  
  assocˡ : Comp C (Comp D E) ⇒ Comp (Comp C D) E
  assocˡ = CC.to-∘ C D ▷ ◇-assocʳ {C = C} {D = D} {Q = Position E}

  assoc⇔ : Comp (Comp C D) E ⇔ Comp C (Comp D E)
  assoc⇔ = mk⇔ assocʳ assocˡ iso₁ iso₂
    where
      iso₁ : assocʳ ∘ assocˡ ≈ id (Comp C (Comp D E))
      iso₁ = with≡ _ _ (λ _ → ≡.refl)

      iso₂ : assocˡ ∘ assocʳ ≈ id (Comp (Comp C D) E)
      iso₂ = with≡ _ _ (λ _ → ≡.refl)

module _ {c c' d d' e e'}
  {C₁ C₂ : Container c c'}
  {D₁ D₂ : Container d d'}
  {E₁ E₂ : Container e e'} where
  
  assoc-nat : ∀ (α : C₁ ⇒ C₂) (β : D₁ ⇒ D₂) (γ : E₁ ⇒ E₂)
        → bimap α (bimap β γ) ∘ assocʳ ≈ assocʳ ∘ bimap (bimap α β) γ
  assoc-nat _ _ _ = with≡ (Comp (Comp C₁ D₁) E₁) (Comp C₂ (Comp D₂ E₂)) (λ _ → ≡.refl)

-- TODO:
-- 
-- semigroupal : {c : Level} → Semigroupal {c = c} {c' = c} Comp map₁ map₂ assoc⇔
-- semigroupal {c} = _

-- Units
module _ {c c'} {C : Container c c'} where
  Id' : Container c c'
  Id' = Id

  unitLeft : Comp Id' C ⇒ C
  unitLeft = CC.from-id ▷ λ p → mk◇ (tt , p)

  ununitLeft : C ⇒ Comp Id' C
  ununitLeft = CC.to-id ▷ λ (mk◇ (_ , p)) → p

  unitRight : Comp C Id' ⇒ C
  unitRight = proj₁ ▷ λ p → mk◇ (p , tt)

  ununitRight : C ⇒ Comp C Id'
  ununitRight = (λ s → s , F.const tt) ▷ λ (mk◇ (p , _)) → p

  unitLeft⇔ : Comp Id' C ⇔ C
  unitLeft⇔ = record {
      to = unitLeft; from = ununitLeft;
      to-from = with≡ C C (λ _ → ≡.refl);
      from-to = with≡ (Comp Id C) (Comp Id C) (λ _ → ≡.refl)
    }

  unitRight⇔ : Comp C Id' ⇔ C
  unitRight⇔ = record {
      to = unitRight; from = ununitRight;
      to-from = with≡ C C (λ _ → ≡.refl);
      from-to = with≡ (Comp C Id) (Comp C Id) (λ _ → ≡.refl)
    }

-- TODO:
-- 
-- monoidal : {c : Level} → Monoidal {c = c} {c' = c} Comp CC.id map₁ map₂ assoc⇔ unitLeft⇔ unitRight⇔
-- monoidal {c} = _