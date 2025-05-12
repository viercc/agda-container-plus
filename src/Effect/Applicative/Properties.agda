
{-# OPTIONS --without-K --safe #-}

module Effect.Applicative.Properties where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

import Relation.Binary.Reasoning.Syntax as Reasoning

import Relation.Binary.PropositionalEquality as ≡
    using (_≡_)

open import Function using (_∘′_; id; _$_)
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
  zipWith-cong f {u₁} {u₂} {v₁} {v₂} u≈ v≈ = <*>-cong (<$>-cong f u≈) v≈

  <*>-cong₁ : ∀ {A} {B} {u₁ u₂ : F (A → B)} {v : F A} → (u₁ ≈ u₂) → (u₁ <*> v ≈ u₂ <*> v)
  <*>-cong₁ u≈ = <*>-cong u≈ refl

  <*>-cong₂ : ∀ {A} {B} {u : F (A → B)} {v₁ v₂ : F A} → (v₁ ≈ v₂) → (u <*> v₁ ≈ u <*> v₂)
  <*>-cong₂ v≈ = <*>-cong refl v≈

  -- convenient equalities
  identity : ∀ {A} (v : F A) → pure id <*> v ≈ v
  identity v =
    begin
      pure id <*> v
    ≈⟨ map id v ⟩
      id <$> v
    ≈⟨ <$>-id v ⟩
      v
    ∎
    where open ≈-Reasoning
  
  pure-naturality : ∀ {A} {B} (f : A → B) (x : A) → f <$> pure x ≈ pure (f x)
  pure-naturality f x =
    begin
      f <$> pure x
    ≈⟨ map f (pure x) ⟨
      pure f <*> pure x
    ≈⟨ homomorphism f x ⟩
      pure (f x)
    ∎
    where
      open ≈-Reasoning
  
  zipWith-pure₁ : ∀ {A} {B} {C} (f : A → B → C) (x : A) (v : F B)
    → zipWith f (pure x) v ≈ f x <$> v
  zipWith-pure₁ f x v =
    begin
      f <$> pure x <*> v
    ≈⟨ <*>-cong₁ (pure-naturality f x) ⟩
      pure (f x) <*> v
    ≈⟨ map (f x) v ⟩
      f x <$> v
    ∎
    where open ≈-Reasoning
  
  zipWith-pure₂ : ∀ {A} {B} {C} (f : A → B → C) (u : F A) (y : B)
    → zipWith f u (pure y) ≈ (λ x → f x y) <$> u
  zipWith-pure₂ f u y =
    begin
      (f <$> u) <*> pure y
    ≈⟨ interchange (f <$> u) y ⟩
      (λ r → r y) <$> (f <$> u)
    ≈⟨ <$>-∘ (λ r → r y) f u ⟩
      (λ x → f x y) <$> u
    ∎
    where open ≈-Reasoning
  
  naturality₁ : ∀ {A B C : Set ℓ} (f : B → C) (u : F (A → B)) (v : F A)
      → f <$> (u <*> v) ≈ f ∘′_ <$> u <*> v
  naturality₁ f u v =
    begin
      f <$> (u <*> v)
    ≈⟨ map f (u <*> v) ⟨
      pure f <*> (u <*> v)
    ≈⟨ composition (pure f) u v ⟨
      _∘′_ <$> pure f <*> u <*> v
    ≈⟨ <*>-cong₁ (zipWith-pure₁ _∘′_ f u) ⟩
      _∘′_ f <$> u <*> v
    ∎
    where open ≈-Reasoning
  
  naturality₂ : ∀ {A B C : Set ℓ} (g : A → B) (u : F (B → C)) (v : F A)
      → (λ f → _∘′_ f g) <$> u <*> v ≈ u <*> (g <$> v)
  naturality₂ g u v =
    begin
      (λ f → _∘′_ f g) <$> u <*> v
    ≈⟨ <*>-cong₁ (zipWith-pure₂ _∘′_ u g) ⟨
      (_∘′_ <$> u) <*> pure g <*> v
    ≈⟨ composition u (pure g) v ⟩
      u <*> (pure g <*> v)
    ≈⟨ <*>-cong₂ (map g v) ⟩
      u <*> (g <$> v)
    ∎
    where open ≈-Reasoning