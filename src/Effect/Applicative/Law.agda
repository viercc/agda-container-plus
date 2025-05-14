{-# OPTIONS --without-K --safe #-}

module Effect.Applicative.Law where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Function using (_∘′_; id; _$_)
open import Effect.Functor
open import Effect.Functor.Law
open import Effect.Applicative

module _
  {ℓ ℓ′}
  (F : Set ℓ → Set ℓ′)
  (_≈_ : ∀ {A : Set ℓ} → Rel (F A) ℓ′)
  (let infix 3 _≈_; _≈_ = _≈_)
  {{ isEquivalence : ∀ {A : Set ℓ} → IsEquivalence (_≈_ {A}) }} where
  
  record IsApplicative (raw : RawApplicative F) : Set (suc (ℓ ⊔ ℓ′)) where
    open RawApplicative raw

    field
      instance
        isFunctor : IsFunctor F _≈_ rawFunctor

    open IsFunctor isFunctor public
    
    field
      <*>-cong : ∀ {A B : Set ℓ} {u₁ u₂ : F (A → B)} {v₁ v₂ : F A}
        → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (u₁ <*> v₁ ≈ u₂ <*> v₂)
      
      map : ∀ {A B : Set ℓ} (f : A → B) (v : F A) → pure f <*> v ≈ f <$> v
      homomorphism : ∀ {A B : Set ℓ} (f : A → B) (x : A) → pure f <*> pure x ≈ pure (f x)
      interchange : ∀ {A B : Set ℓ} (u : F (A → B)) (y : A) → u <*> pure y ≈ (λ f → f y) <$> u
      composition : ∀ {A B C : Set ℓ} (u : F (B → C)) (v : F (A → B)) (w : F A)
        → _∘′_ <$> u <*> v <*> w ≈ u <*> (v <*> w)
  
  record Applicative : Set (suc (ℓ ⊔ ℓ′)) where
    field
      instance
        rawApplicative : RawApplicative F
        isApplicative : IsApplicative rawApplicative
    
    open RawApplicative rawApplicative public
    open IsApplicative isApplicative public

    functor : Functor F _≈_
    functor = record { rawFunctor = rawFunctor; isFunctor = isFunctor }