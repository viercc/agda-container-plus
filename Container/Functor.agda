{-# OPTIONS --without-K --safe #-}

module Container.Functor where

open import Level

open import Function using (_∘_; id; _$_)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using ()
    renaming (_≡_ to infix 3 _≡_)

open import Data.Container.Core
import Data.Container.Properties as ContProp
open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)
import Data.Container.Relation.Binary.Equality.Setoid as CSetoid

open import Effect.Functor
open import Effect.Functor.Law

private
  variable
    s p e : Level

Eq' : (Con : Container s p) {A : Set e} → Rel (⟦ Con ⟧ A) (s ⊔ p ⊔ e)
Eq' Con {A} = CSetoid.Eq (P.setoid A) Con

isEquivalence' : (Con : Container s p) {A : Set e} → IsEquivalence (Eq' Con {A = A})
isEquivalence' Con {A} = CSetoid.isEquivalence (P.setoid A) Con

rawFunctor⟦_⟧ : (Con : Container s p) → RawFunctor {ℓ = e} (⟦ Con ⟧) 
rawFunctor⟦_⟧ Con = record { _<$>_ = map }

isFunctor⟦_⟧ : (Con : Container s p) → {e : Level} → IsFunctor {ℓ = e} ⟦ Con ⟧ (rawFunctor⟦ Con ⟧)
isFunctor⟦_⟧ Con {e} = record {isFunctor} where
  module isFunctor where
    open RawFunctor (rawFunctor⟦ Con ⟧)
    infix 3 _≈_
    
    _≈_ = Eq' {e = e} Con
    isEquivalence = isEquivalence' {e = e} Con

    map-cong : ∀  {A B : Set e} (f : A → B) {u₁ u₂ : ⟦ Con ⟧ A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
    map-cong f (Pw s≡ pos≗) = Pw s≡ (λ p → P.cong f (pos≗ p))

    map-id : ∀ {A : Set e} (x : ⟦ Con ⟧ A) → (id <$> x ≈ x)
    map-id {A = A} x = ContProp.map-identity (P.setoid A) x

    map-∘  : ∀ {A B C : Set e} (f : B → C) (g : A → B) (x : ⟦ Con ⟧ A)
      → (f <$> (g <$> x) ≈ (f ∘ g) <$> x)
    map-∘ {C = C} f g x = ContProp.map-compose (P.setoid C) f g x
