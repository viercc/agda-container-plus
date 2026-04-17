{-# OPTIONS --without-K --safe #-}

module Effect.Functor.Law where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence; _⇒_; _⇔_)

open import Function using (_∘_; _∘′_; id; _$_)
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

  pack : Set ℓ → Setoid ℓ′ ℓ′
  pack A = record { isEquivalence = isEquivalence {A} }

module unpack {ℓ ℓ′} (Fi : Set ℓ → Setoid ℓ′ ℓ′) where
  F : Set ℓ → Set ℓ′
  F A = Setoid.Carrier (Fi A)

  infix 3 _≈_

  _≈_ : {A : Set ℓ} → Rel (F A) ℓ′
  _≈_ {A} = Setoid._≈_ (Fi A)

  instance
    isEquivalence : {A : Set ℓ} → IsEquivalence (_≈_ {A})
    isEquivalence {A} = Setoid.isEquivalence (Fi A)

module _ {ℓ ℓ′} (Fi : Set ℓ → Setoid ℓ′ ℓ′) where
  open unpack Fi

  IsFunctorS : RawFunctor F → Set (suc (ℓ ⊔ ℓ′))
  IsFunctorS raw = IsFunctor F _≈_ raw

  FunctorS : Set (suc (ℓ ⊔ ℓ′))
  FunctorS = Functor F _≈_

module _ {ℓ ℓ′}
  (F : Set ℓ → Set ℓ′)
  (_≈₁_ _≈₂_ : ∀ {A : Set ℓ} → Rel (F A) ℓ′)
  (let infix 3 _≈₁_; _≈₁_ = _≈₁_)
  (let infix 3 _≈₂_; _≈₂_ = _≈₂_)
  {{ isEquivalence₁ : ∀ {A : Set ℓ} → IsEquivalence (_≈₁_ {A}) }}
  {{ isEquivalence₂ : ∀ {A : Set ℓ} → IsEquivalence (_≈₂_ {A}) }}
  where

  transferIsFunctor : (∀ {A} → _≈₁_ {A} ⇔ _≈₂_ {A} ) → {raw : RawFunctor F}
    → IsFunctor F _≈₁_ raw → IsFunctor F _≈₂_ raw
  transferIsFunctor eqv {raw = raw} isFunctor₁ =
      record {
        <$>-cong = λ f eq → ≈-to (<$>-cong f (≈-from eq));
        <$>-id = λ x → ≈-to (<$>-id x);
        <$>-∘ = λ f g x → ≈-to (<$>-∘ f g x)
      }
    where
      open RawFunctor raw
      open IsFunctor isFunctor₁
      open import Data.Product using (proj₁; proj₂)

      ≈-to : ∀ {A} {x y : F A} → x ≈₁ y → x ≈₂ y
      ≈-to = proj₁ eqv
      ≈-from : ∀ {A} {x y : F A} → x ≈₂ y → x ≈₁ y
      ≈-from = proj₂ eqv

  transfer : (∀ {A} → _≈₁_ {A} ⇔ _≈₂_ {A} ) → Functor F _≈₁_ → Functor F _≈₂_
  transfer eqv functor₁ = record {
      rawFunctor = Functor.rawFunctor functor₁;
      isFunctor = transferIsFunctor eqv (Functor.isFunctor functor₁)
    }