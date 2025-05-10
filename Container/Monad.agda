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
open CM using (id; _∘_)

import Data.Container.Combinator as CC -- Container Combinator

open CC using () renaming (_∘_ to Comp)

open import Container.Combinator.Properties

private
  variable
    s p : Level

Id : Container Level.zero Level.zero
Id = CC.id

-- Raw (without law) definition

record RawMonad (C : Container s p) : Set (suc (s ⊔ p)) where
  open Container C renaming (Shape to S; Position to P) public
  
  field
    unit : Id ⇒ C
    join : Comp C C ⇒ C

record RawMonad' (C : Container s p) : Set (suc (s ⊔ p)) where
  open Container C renaming (Shape to S; Position to P) public

  infixr 2 _•_
  
  field
    ε : S
    _•_ : (s : S) → (P s → S) → S
    ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
    ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))

RawMonad'-to-RawMonad : ∀ {C : Container s p} (rawMonad' : RawMonad' C) → RawMonad C
RawMonad'-to-RawMonad {C = C} rawMonad' = record{ unit = unit; join = join }
  where
    open RawMonad' rawMonad'

    unit : Id ⇒ C
    unit = F.const ε ▷ F.const tt

    join : Comp C C ⇒ C
    join .shape (s , v) = s • v
    join .position {s = s , v} p = mk◇ (↖ p , ↗ p)

RawMonad-to-RawMonad' : ∀ {C : Container s p} (rawMonad : RawMonad C) → RawMonad' C
RawMonad-to-RawMonad' rawMonad = record {rawMonadImpl'}
  where
    module rawMonadImpl' where
      open RawMonad rawMonad

      ε : S
      ε = shape unit tt

      _•_ : (s : S) → (P s → S) → S
      _•_ s v = shape join (s , v)

      ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
      ↖ {s} {v} p = proj₁ (◇.proof (position join { s = s , v } p))

      ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))
      ↗ {s} {v} p = proj₂ (◇.proof (position join {s = s , v } p))

-- Monad laws

record IsMonad (C : Container s p) (raw : RawMonad C) : Set (suc (s ⊔ p)) where
  open RawMonad raw
  module Comp = ∘-Properties

  field
    unit-left : ∀ {X : Set p} {xs : ⟦ C ⟧ X}
      → ⟪ join ∘ Comp.map₁ unit ∘ Comp.Compλ ⟫ xs ≡ xs
    
    unit-right : ∀ {X : Set p} {xs : ⟦ C ⟧ X}
      → ⟪ join ∘ Comp.map₂ unit ∘ Comp.Compρ ⟫ xs ≡ xs