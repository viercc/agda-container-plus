{-# OPTIONS --without-K --safe #-}

module Container.Monad where

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

import Data.Container.Morphism as CM   -- Container Morphism
open CM using (id; _∘_)

import Data.Container.Combinator as CC -- Container Combinator

open CC using () renaming (_∘_ to Comp)

open import Container.Morphism.Equality
open import Container.Morphism.Iso
open import Container.Combinator.Properties

private
  variable
    s p : Level

-- Monad as monoid with respect to Comp

module AsMonoid where
  record RawMonad (C : Container s p) : Set (s ⊔ p) where
    open Container C renaming (Shape to S; Position to P) public
    
    field
      unit : Id ⇒ C
      join : Comp C C ⇒ C

  record IsMonad (C : Container s p) (raw : RawMonad C) : Set (s ⊔ p) where
    open RawMonad raw
    open ∘-Properties using (map₁; map₂)
    
    leftId⇒ : C ⇒ Comp Id C
    leftId⇒ = ∘-Properties.leftId ._⇔_.to

    rightId⇒ : C ⇒ Comp C Id
    rightId⇒ = ∘-Properties.rightId {C = C} ._⇔_.to

    assoc⇒ : Comp (Comp C C) C ⇒ Comp C (Comp C C)
    assoc⇒ = ∘-Properties.assoc ._⇔_.to

    field
      left-unit : join ∘ map₁ unit ∘ leftId⇒ ≈ id C
      right-unit : join ∘ map₂ unit ∘ rightId⇒ ≈ id C
      assoc : join ∘ map₁ join ≈ join ∘ map₂ join ∘ assoc⇒

-- Uustalu-style description of Containers ∩ Monads
module Uustalu where
  
  record RawMonad (C : Container s p) : Set (s ⊔ p) where
    open Container C renaming (Shape to S; Position to P) public

    infixr 7 _•_
    
    field
      ε : S
      _•_ : (s : S) → (P s → S) → S
      ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
      ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))
    
  record IsMonad (C : Container s p) (raw : RawMonad C) : Set (s ⊔ p) where
    open RawMonad raw

    diag : ∀ {s : S} {v : P s → S} (w : (p₁ : P s) → P (v p₁) → S)
      → P (s • v) → S
    diag {s} {v} w p = w (↖ p) (↗ p)

    field
      •-ε : ∀ (s : S) → s • F.const ε ≡ s
      ε-• : ∀ (s : S) → ε • F.const s ≡ s
      •-• : ∀ (s : S) (v : P s → S) (w : (p : P s) → P (v p) → S)
        → (s • v) • diag w ≡ s • (λ p → v p • w p)
      
      ↖-inner-ε : ∀ {s : S} (p : P (s • F.const ε))
        → ↖ p ≡ ≡.subst P (•-ε s) p
      ↗-outer-ε : ∀ {s : S} (p : P (ε • F.const s))
        → ↗ p ≡ ≡.subst P (ε-• s) p
      
      ↖-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
        → {p : P ((s • v) • diag w)} {q : P (s • (λ q₁ → v q₁ • w q₁))}
        → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
        → ↖ (↖ p) ≡ ↖ q
      ↗-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
        → {p : P ((s • v) • diag w)} {q : P (s • (λ q₁ → v q₁ • w q₁))}
        → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
        → (let p₁₁≡q₁ = ↖-↖ p≡q)
        → ≡.subst (λ r → P (v r)) p₁₁≡q₁ (↗ (↖ p)) ≡ ↖ (↗ q)
      ↗-↗ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
        → {p : P ((s • v) • diag w)} {q : P (s • (λ q₁ → v q₁ • w q₁))}
        → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
        → (let p₁₁≡q₁ = ↖-↖ p≡q)
           (let p₁₂≡q₂₁ = ↗-↖ p≡q)
        → ≡.dsubst₂ (λ r₁ r₂ → P (w r₁ r₂)) p₁₁≡q₁ p₁₂≡q₂₁ (↗ p) ≡ ↗ (↗ q)

from-Uustalu : ∀ {C : Container s p} (rawMonad' : Uustalu.RawMonad C) → AsMonoid.RawMonad C
from-Uustalu {C = C} rawMonad' = record{ unit = unit; join = join }
  where
    open Uustalu.RawMonad rawMonad'

    unit : Id ⇒ C
    unit = F.const ε ▷ F.const tt

    join : Comp C C ⇒ C
    join .shape (s , v) = s • v
    join .position {s = s , v} p = mk◇ (↖ p , ↗ p)

to-Uustalu : ∀ {C : Container s p} (rawMonad : AsMonoid.RawMonad C) → Uustalu.RawMonad C
to-Uustalu rawMonad = record {rawMonadImpl'}
  where
    module rawMonadImpl' where
      open AsMonoid.RawMonad rawMonad

      ε : S
      ε = shape unit tt

      _•_ : (s : S) → (P s → S) → S
      _•_ s v = shape join (s , v)

      ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
      ↖ {s} {v} p = proj₁ (◇.proof (position join { s = s , v } p))

      ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))
      ↗ {s} {v} p = proj₂ (◇.proof (position join {s = s , v } p))
