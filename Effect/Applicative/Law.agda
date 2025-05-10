{-# OPTIONS --without-K --safe #-}

module Effect.Applicative.Law where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using () renaming (_≡_ to infix 3 _≡_)

open import Function using (_∘_; id; _$_)
open import Effect.Functor
open import Effect.Functor.Law
open import Effect.Applicative

private
  variable
    ℓ ℓ′ : Level

comp : ∀ {a} {A : Set a} {b} {B : Set b} {c} {C : Set c} →
    (B -> C) -> (A -> B) -> (A -> C)
comp f g = f ∘ g

record IsApplicative (F : Set ℓ → Set ℓ′) (raw : RawApplicative F) : Set (suc (ℓ ⊔ ℓ′)) where
  open RawApplicative raw

  field
    isFunctor : IsFunctor F rawFunctor

  open IsFunctor isFunctor public

  field
    ap-cong : ∀ {A B : Set ℓ} {u₁ u₂ : F (A → B)} {v₁ v₂ : F A}
      → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (u₁ <*> v₁ ≈ u₂ <*> v₂)
    
    ap-map : ∀ {A B : Set ℓ} (f : A → B) (v : F A) → pure f <*> v ≈ f <$> v
    ap-homomorphism : ∀ {A B : Set ℓ} (f : A → B) (x : A) → pure f <*> pure x ≈ pure (f x)
    ap-interchange : ∀ {A B : Set ℓ} (u : F (A → B)) (y : A) → u <*> pure y ≈ (λ f → f y) <$> u
    ap-composition : ∀ {A B C : Set ℓ} (u : F (B → C)) (v : F (A → B)) (w : F A)
      → comp <$> u <*> v <*> w ≈ u <*> (v <*> w)
