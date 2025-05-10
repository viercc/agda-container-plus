
{-# OPTIONS --without-K --safe #-}

module Effect.Applicative.Properties where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

import Relation.Binary.Reasoning.Syntax as Reasoning

import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using () renaming (_≡_ to infix 3 _≡_)

open import Function using (_∘_; id; _$_)
open import Effect.Functor
open import Effect.Functor.Law
open import Effect.Applicative
open import Effect.Applicative.Law

private
  variable
    ℓ ℓ′ : Level

module properties (F : Set ℓ → Set ℓ′) (raw : RawApplicative F) (isApplicative : IsApplicative F raw) where
  open RawApplicative raw
  open IsApplicative isApplicative
  open IsEquivalence {{...}}
  
  module ≈-Reasoning {A : Set ℓ} where
    private
      eqv : Rel (F A) ℓ′
      eqv = _≈_ {A = A}
    open Reasoning.begin-syntax eqv id public
    open Reasoning.≈-syntax eqv eqv trans sym public
    open Reasoning.end-syntax eqv refl public

  -- congruences

  pure-cong : ∀ {A} {x y : A} → x ≡ y → pure x ≈ pure y
  pure-cong x≡y = reflexive (P.cong pure x≡y)
  
  zipWith-cong : ∀ {A B C : Set ℓ} (f : A → B → C) {u₁ u₂ : F A} {v₁ v₂ : F B}
    → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (zipWith f u₁ v₁ ≈ zipWith f u₂ v₂)
  zipWith-cong f {u₁} {u₂} {v₁} {v₂} u≈ v≈ = ap-cong (map-cong f u≈) v≈

  ap-cong₁ : ∀ {A} {B} {u₁ u₂ : F (A → B)} {v : F A} → (u₁ ≈ u₂) → (u₁ <*> v ≈ u₂ <*> v)
  ap-cong₁ u≈ = ap-cong u≈ refl

  ap-cong₂ : ∀ {A} {B} {u : F (A → B)} {v₁ v₂ : F A} → (v₁ ≈ v₂) → (u <*> v₁ ≈ u <*> v₂)
  ap-cong₂ v≈ = ap-cong refl v≈

  -- convenient equalities
  ap-identity : ∀ {A} (v : F A) → pure id <*> v ≈ v
  ap-identity v =
    begin
      pure id <*> v
    ≈⟨ ap-map id v ⟩
      id <$> v
    ≈⟨ map-id v ⟩
      v
    ∎
    where open ≈-Reasoning
  
  pure-naturality : ∀ {A} {B} (f : A → B) (x : A) → f <$> pure x ≈ pure (f x)
  pure-naturality f x =
    begin
      f <$> pure x
    ≈⟨ ap-map f (pure x) ⟨
      pure f <*> pure x
    ≈⟨ ap-homomorphism f x ⟩
      pure (f x)
    ∎
    where
      open ≈-Reasoning
  
  zipWith-pure₁ : ∀ {A} {B} {C} (f : A → B → C) (x : A) (v : F B)
    → zipWith f (pure x) v ≈ f x <$> v
  zipWith-pure₁ f x v =
    begin
      f <$> pure x <*> v
    ≈⟨ ap-cong₁ (pure-naturality f x) ⟩
      pure (f x) <*> v
    ≈⟨ ap-map (f x) v ⟩
      f x <$> v
    ∎
    where open ≈-Reasoning
  
  zipWith-pure₂ : ∀ {A} {B} {C} (f : A → B → C) (u : F A) (y : B)
    → zipWith f u (pure y) ≈ (λ x → f x y) <$> u
  zipWith-pure₂ f u y =
    begin
      (f <$> u) <*> pure y
    ≈⟨ ap-interchange (f <$> u) y ⟩
      (λ r → r y) <$> (f <$> u)
    ≈⟨ map-∘ (λ r → r y) f u ⟩
      (λ x → f x y) <$> u
    ∎
    where open ≈-Reasoning
  
  ap-naturality₁ : ∀ {A B C : Set ℓ} (f : B → C) (u : F (A → B)) (v : F A)
      → f <$> (u <*> v) ≈ comp f <$> u <*> v
  ap-naturality₁ f u v =
    begin
      f <$> (u <*> v)
    ≈⟨ ap-map f (u <*> v) ⟨
      pure f <*> (u <*> v)
    ≈⟨ ap-composition (pure f) u v ⟨
      comp <$> pure f <*> u <*> v
    ≈⟨ ap-cong₁ (zipWith-pure₁ comp f u) ⟩
      comp f <$> u <*> v
    ∎
    where open ≈-Reasoning
  
  ap-naturality₂ : ∀ {A B C : Set ℓ} (g : A → B) (u : F (B → C)) (v : F A)
      → (λ f → comp f g) <$> u <*> v ≈ u <*> (g <$> v)
  ap-naturality₂ g u v =
    begin
      (λ f → comp f g) <$> u <*> v
    ≈⟨ ap-cong₁ (zipWith-pure₂ comp u g) ⟨
      (comp <$> u) <*> pure g <*> v
    ≈⟨ ap-composition u (pure g) v ⟩
      u <*> (pure g <*> v)
    ≈⟨ ap-cong₂ (ap-map g v) ⟩
      u <*> (g <$> v)
    ∎
    where open ≈-Reasoning