{-# OPTIONS --without-K --safe #-}

module Container.Morphism.Iso where

open import Level

import Relation.Binary.PropositionalEquality as P
open P using (_≡_; _≗_)

import Function as F
open F using (id; _∘_)
import Data.Product as Prod
open Prod using (Σ; _,_)
open import Data.Product.Properties
  using (Σ-≡,≡←≡)

open import Data.Container.Core
import Data.Container.Relation.Binary.Equality.Setoid as CEq
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise)
  renaming (_,_ to mkPointwise)

import Data.Container.Morphism as CM

-- Also re-exports
open import Container.Morphism.Equality
  using (_≈_; mk≈) public

module _ {s₁ p₁ s₂ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where

  record _⇔_ : Set (s₁ ⊔ p₁ ⊔ s₂ ⊔ p₂) where
    constructor mk⇔
    field
      to : C₁ ⇒ C₂
      from : C₂ ⇒ C₁
      to-from : to CM.∘ from ≈ CM.id C₂
      from-to : from CM.∘ to ≈ CM.id C₁
