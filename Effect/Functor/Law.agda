{-# OPTIONS --without-K --safe #-}

module Effect.Functor.Law where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Function using (_∘_; id; _$_)
open import Effect.Functor


private
  variable
    ℓ ℓ′ : Level
    A B C X Y : Set ℓ

record IsFunctor (F : Set ℓ → Set ℓ′) (raw : RawFunctor F) : Set (suc (ℓ ⊔ ℓ′)) where
  infix 3 _≈_
  
  open RawFunctor raw

  field
    _≈_ : Rel (F A) ℓ′
    instance isEquivalence : ∀ {A : Set ℓ} → IsEquivalence (_≈_ {A = A})
    
    map-cong : ∀ (f : A → B) {u₁ u₂ : F A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
    
    map-id : ∀ (x : F A) → (id <$> x ≈ x)
    map-∘  : ∀ (f : B → C) (g : A → B) (x : F A)
      → (f <$> (g <$> x) ≈ (f ∘ g) <$> x)
