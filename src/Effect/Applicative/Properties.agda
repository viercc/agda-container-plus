
{-# OPTIONS --without-K --safe #-}

module Effect.Applicative.Properties where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

import Relation.Binary.Reasoning.Setoid as Reasoning

open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_)

open import Function using (_∘′_; id; _$_)
open import Effect.Functor
open import Effect.Functor.Law
open import Effect.Applicative
open import Effect.Applicative.Law

module properties {ℓ ℓ′} (F : Set ℓ → Set ℓ′) (applicative : Applicative F) where
  open Applicative applicative
  open IsEquivalence {{...}}
  module ≈-Reasoning {A : Set ℓ} = Reasoning (setoid A)
  
  -- congruences

  pure-cong : ∀ {A} {x y : A} → x ≡ y → pure x ≈ pure y
  pure-cong x≡y = reflexive (≡.cong pure x≡y)
  
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
      → (_∘′ g) <$> u <*> v ≈ u <*> (g <$> v)
  naturality₂ g u v =
    begin
      (_∘′ g) <$> u <*> v
    ≈⟨ <*>-cong₁ (zipWith-pure₂ _∘′_ u g) ⟨
      (_∘′_ <$> u) <*> pure g <*> v
    ≈⟨ composition u (pure g) v ⟩
      u <*> (pure g <*> v)
    ≈⟨ <*>-cong₂ (map g v) ⟩
      u <*> (g <$> v)
    ∎
    where open ≈-Reasoning


module _ where

  {-
    Old tale: In Haskell, the type class Applicative used to be defined by
    the following formulation, which _never_ mentions the underlying Functor.

    It was because Applicative was not a subclass of Functor, but independent class
    such that

    - their methods (pure, _<*>_) can make it Functor (_<$>_) by itself
    - their laws (identity, homomorphism, interchange, composition) can prove
      Functor laws by itself
    
  -}
  record BareApplicative {ℓ ℓ′} (F : Set ℓ → Set ℓ′) : Set (suc (ℓ ⊔ ℓ′)) where
    infixl 4 _<*>_
    infix 3 _≈_

    field
      -- Minimal operations to define RawFunctor + RawApplicative
      pure : ∀ {A} → A → F A
      _<*>_ : ∀ {A B} → F (A → B) → F A → F B

      -- Notion of equivalence is needed anyway
      _≈_ : ∀ {A} → Rel (F A) ℓ′
      instance
        isEquivalence : {A : Set ℓ} → IsEquivalence (_≈_ {A = A})
      
      -- Minimal additional property to define IsFunctor + IsApplicative
      
      <*>-cong : ∀ {A B : Set ℓ} {u₁ u₂ : F (A → B)} {v₁ v₂ : F A}
        → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (u₁ <*> v₁ ≈ u₂ <*> v₂)
      identity : ∀ {A} (x : F A) → pure id <*> x ≈ x 
      homomorphism : ∀ {A B : Set ℓ} (f : A → B) (x : A) → pure f <*> pure x ≈ pure (f x)
      interchange : ∀ {A B : Set ℓ} (u : F (A → B)) (y : A) → u <*> pure y ≈ pure (λ f → f y) <*> u
      composition : ∀ {A B C : Set ℓ} (u : F (B → C)) (v : F (A → B)) (w : F A)
        → pure _∘′_ <*> u <*> v <*> w ≈ u <*> (v <*> w)
    
    setoid : (A : Set ℓ) → Setoid ℓ′ ℓ′
    setoid A = record { isEquivalence = isEquivalence {A = A} }

  mkApplicative : ∀ {ℓ ℓ′} {F : Set ℓ → Set ℓ′} → BareApplicative F → Applicative F
  mkApplicative {ℓ} {ℓ′} {F = F} bare = record { rawApplicative = raw; isApplicative = record {isApplicativeImpl} }
    where
      open IsEquivalence {{...}}
      
      module ≈-Reasoning {A : Set ℓ} = Reasoning (BareApplicative.setoid bare A)
      
      raw = mkRawApplicative F (bare .BareApplicative.pure) (bare .BareApplicative._<*>_)

      module isApplicativeImpl where
        open BareApplicative bare public
        open RawApplicative raw using (rawFunctor; _<$>_)

        -- Functor laws can be derived from BareApplicative
        
        <$>-cong : ∀ {A B} (f : A → B) {u₁ u₂ : F A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
        <$>-cong f u₁≈u₂ = <*>-cong refl u₁≈u₂

        <$>-id : ∀ {A} (x : F A) → (id <$> x ≈ x)
        <$>-id x = identity x
        
        <$>-∘ : ∀ {A B C} (f : B → C) (g : A → B) (x : F A) → (f <$> (g <$> x) ≈ (f ∘′ g) <$> x)
        <$>-∘ f g x = begin
            f <$> (g <$> x)
          ≈⟨ refl ⟩
            pure f <*> (pure g <*> x)
          ≈⟨ composition (pure f) (pure g) x ⟨
            pure _∘′_ <*> pure f <*> pure g <*> x
          ≈⟨ <*>-cong (<*>-cong (homomorphism _ _) refl) refl ⟩
            pure (f ∘′_) <*> pure g <*> x
          ≈⟨ <*>-cong (homomorphism _ _) refl ⟩
            pure (f ∘′ g) <*> x
          ≈⟨ refl ⟩
            f ∘′ g <$> x
          ∎
          where open ≈-Reasoning
        
        isFunctor : IsFunctor F rawFunctor
        isFunctor = record {
            isEquivalence = isEquivalence;
            <$>-cong = <$>-cong;
            <$>-id = <$>-id;
            <$>-∘ = <$>-∘
          }

        -- map is definitionally true
        map : ∀ {A B} (f : A → B) (v : F A) → pure f <*> v ≈ f <$> v
        map _ _ = refl