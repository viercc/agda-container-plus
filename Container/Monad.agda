{-# OPTIONS --without-K --safe #-}

module Container.Monad where

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

open CC using () renaming (_∘_ to Comp)

private
  variable
    s p : Level

Id : Container Level.zero Level.zero
Id = CC.id

record RawMonad (C : Container s p) : Set (suc (s ⊔ p)) where
  open Container C renaming (Shape to S; Position to P) public

  infixr 2 _•_
  
  field
    ε : S
    _•_ : (s : S) → (P s → S) → S
    ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
    ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))

module _ {C : Container s p} (rawMonad : RawMonad C) where
  open RawMonad rawMonad

  unit : Id ⇒ C
  unit = F.const ε ▷ F.const tt

  join : Comp C C ⇒ C
  join .shape (s , v) = s • v
  join .position {s = s , v} p = mk◇ (↖ p , ↗ p)

extractRawMonad : ∀ {C : Container s p}
  → (Id ⇒ C) → (Comp C C ⇒ C) → RawMonad C
extractRawMonad {C = C} unit join = record {rawMonadImpl}
  where
    module rawMonadImpl where
      open Container C renaming (Shape to S; Position to P) public

      ε : S
      ε = shape unit tt

      _•_ : (s : S) → (P s → S) → S
      _•_ s v = shape join (s , v)

      ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
      ↖ {s} {v} p = proj₁ (◇.proof (position join { s = s , v } p))

      ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))
      ↗ {s} {v} p = proj₂ (◇.proof (position join {s = s , v } p))