{-# OPTIONS --without-K --safe #-}

module Effect.Functor.Law where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Function using (_∘_; id; _$_)
open import Effect.Functor

module _ {ℓ ℓ′}
  (F : Set ℓ → Set ℓ′)
  (_≈_ : ∀ {A : Set ℓ} → Rel (F A) ℓ′)
  (let infix 3 _≈_; _≈_ = _≈_)
  {{ isEquivalence : ∀ {A : Set ℓ} → IsEquivalence (_≈_ {A}) }}
  where

  record IsFunctor (raw : RawFunctor F) : Set (suc (ℓ ⊔ ℓ′)) where
    
    open RawFunctor raw
    
    field
      <$>-cong : ∀ {A B : Set ℓ} (f : A → B) {u₁ u₂ : F A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
      
      <$>-id : ∀ {A : Set ℓ} (x : F A) → (id <$> x ≈ x)
      <$>-∘  : ∀ {A B C : Set ℓ} (f : B → C) (g : A → B) (x : F A)
        → (f <$> (g <$> x) ≈ (f ∘ g) <$> x)

  record Functor : Set (suc (ℓ ⊔ ℓ′)) where
    field
      instance 
        rawFunctor : RawFunctor F
        isFunctor : IsFunctor rawFunctor
    
    open RawFunctor rawFunctor public
    open IsFunctor isFunctor public