{-# OPTIONS --without-K --safe #-}

module Effect.Functor.Law where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Function using (_∘_; id; _$_)
open import Effect.Functor

record IsFunctor
  {ℓ ℓ′}
  (F : Set ℓ → Set ℓ′)
  (_∼_ : ∀ {A : Set ℓ} → Rel (F A) ℓ′)
  {{ isEquivalence : ∀ {A : Set ℓ} → IsEquivalence (_∼_ {A}) }}
  (raw : RawFunctor F)
    : Set (suc (ℓ ⊔ ℓ′)) where
  
  infix 3 _≈_
  _≈_ : ∀ {A : Set ℓ} → Rel (F A) ℓ′
  _≈_ = _∼_
  
  open RawFunctor raw
  
  field
    <$>-cong : ∀ {A B : Set ℓ} (f : A → B) {u₁ u₂ : F A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
    
    <$>-id : ∀ {A : Set ℓ} (x : F A) → (id <$> x ≈ x)
    <$>-∘  : ∀ {A B C : Set ℓ} (f : B → C) (g : A → B) (x : F A)
      → (f <$> (g <$> x) ≈ (f ∘ g) <$> x)
  
  setoid : ∀ (A : Set ℓ) → Setoid ℓ′ ℓ′
  setoid A = record { Carrier = F A; isEquivalence = isEquivalence {A = A} }

record Functor
  {ℓ ℓ′}
  (F : Set ℓ → Set ℓ′)
  (_≈_ : ∀ {A : Set ℓ} → Rel (F A) ℓ′)
  {{ isEquivalence : ∀ {A : Set ℓ} → IsEquivalence (_≈_ {A}) }}
    : Set (suc (ℓ ⊔ ℓ′)) where
  field
    instance 
      rawFunctor : RawFunctor F
      isFunctor : IsFunctor F _≈_ rawFunctor
  
  open RawFunctor rawFunctor public
  open IsFunctor isFunctor public