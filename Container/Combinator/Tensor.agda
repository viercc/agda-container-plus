{-# OPTIONS --without-K --safe #-}

module Container.Combinator.Tensor where


open import Level using (Level; _⊔_; lower)
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product.Base as Product using (_,_; <_,_>; proj₁; proj₂; ∃)
open import Data.Sum.Base as Sum using ([_,_]′)
open import Data.Unit.Polymorphic.Base using (⊤)
import Function.Base as F

open import Data.Container.Core
open import Data.Container.Relation.Unary.Any

module _ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  infixr 2 _⊗_

  _⊗_ : Container (s₁ ⊔ s₂) (p₁ ⊔ p₂)
  _⊗_ .Shape = Shape C₁ Product.× Shape C₂
  _⊗_ .Position = Product.uncurry λ s₁ s₂ → (Position C₁ s₁) Product.× (Position C₂ s₂)

  to-⊗ : ∀ {a} {A₁ A₂ B : Set a} → (A₁ → A₂ → B) → ⟦ C₁ ⟧ A₁ → ⟦ C₂ ⟧ A₂ → ⟦ _⊗_ ⟧ B
  to-⊗ op (s₁ , f₁) (s₂ , f₂) = ((s₁ , s₂) , Product.uncurry λ p₁ p₂ → op (f₁ p₁) (f₂ p₂))

  -- Day convolution for Functor is not yet implemented
  -- 
  -- from-⊗ : ∀ {a} {A : Set a} → ⟦ _⊗_ ⟧ A → Day ⟦ C₁ ⟧ ⟦ C₂ ⟧ A
  -- from-⊗ ((s₁ , s₂) , f) = _