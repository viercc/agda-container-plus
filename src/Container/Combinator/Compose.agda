{-# OPTIONS --without-K --safe #-}

-- Container compositions
-- Reexports from Data.Container.Combinator and additional functions
module Container.Combinator.Compose where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Core renaming (map to map⟦⟧)
open import Data.Container.Morphism using (id; _∘_)
import Data.Container.Combinator as CC
open CC using ()
  renaming (id to Id; _∘_ to Comp; to-∘ to to-Comp; from-∘ to from-Comp)
  public

private
  variable
    c c' d d' e e' f f' : Level

module ◇-util where
  open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_)
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

bimap : ∀ {C₁ C₂ : Container c c'} {D₁ D₂ : Container d d'}
    → (C₁ ⇒ C₂) → (D₁ ⇒ D₂) → Comp C₁ D₁ ⇒ Comp C₂ D₂
bimap α β = map₁ α ∘ map₂ β

open ◇-util

-- Associativity

module _ {c c' d d' e e'}
  {C : Container c c'}
  {D : Container d d'}
  {E : Container e e'} where
  assocʳ : Comp (Comp C D) E ⇒ Comp C (Comp D E)
  assocʳ = from-Comp C D ▷ ◇-assocˡ {C = C} {D = D} {Q = Position E}
  
  assocˡ : Comp C (Comp D E) ⇒ Comp (Comp C D) E
  assocˡ = to-Comp C D ▷ ◇-assocʳ {C = C} {D = D} {Q = Position E}

-- Units
module _ {c c'} {C : Container c c'} where
  private
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
