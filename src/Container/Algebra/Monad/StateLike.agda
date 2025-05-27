{-# OPTIONS --without-K --safe #-}

-- StateLike monad, a subclass of Monomial monad
module Container.Algebra.Monad.StateLike where

open import Level

import Function as F
open F using (_∘′_; id)
import Data.Product as Prod
open Prod using (Σ; proj₁; proj₂; _,_)
open import Data.Empty
open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_)
import Data.Bool.Properties as BoolProp

open import Relation.Binary
  using (IsEquivalence; Setoid; DecidableEquality)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≢_; _≗_)
open import Relation.Nullary
  using (Dec; does; yes; no; ⌊_⌋)

open import Data.Container.Core

open import Container.Algebra.Monad.Monomial

private
  variable
    m p : Level

record RawStateLike (M : Set m) (I : Set p) : Set (m ⊔ p) where
  infixr 7 _•_
  
  field
    ε : M
    _•_ : M → (I → M) → M
    t : I → M → I

record IsStateLike (M : Set m) (I : Set p) (raw : RawStateLike M I) : Set (m ⊔ p) where
  open RawStateLike raw

  diag : M → (I → I → M) → (I → M)
  diag m w i = w i (t i m)

  zip : (I → M) → (I → I → M) → (I → M)
  zip v w i = v i • w i

  field
    •-cong₂ : ∀ {m : M} {f g : I → M} → f ≗ g → m • f ≡ m • g

    •-ε : ∀ (m : M) → m • F.const ε ≡ m
    ε-• : ∀ (m : M) → ε • F.const m ≡ m
    •-• : ∀ (m : M) (v : I → M) (w : I → I → M)
      → (m • v) • diag m w ≡ m • zip v w

    t-ε : ∀ (i : I) → t i ε ≡ i
    
    t-• : ∀ (m : M) (v : I → M)
      → (i : I)
      → t i (m • v) ≡ t (t i m) (v i)

-- StateLike is a special Monomial

module _ {M : Set m} {I : Set p} where
  toRawMonad' : RawStateLike M I → RawMonad' M I
  toRawMonad' rawSL = record {
      ε = ε;
      _•_ = _•_; 
      ql = λ _ _ i → i;
      qr = λ m _ i → t i m 
    }
    where open RawStateLike rawSL
  
  toIsMonad' : (rawSL : RawStateLike M I)
    → IsStateLike M I rawSL → IsMonad' M I (toRawMonad' rawSL)
  toIsMonad' rawSL isSL = record {
      •-cong₂ = •-cong₂;
      ql-cong₂ = λ _ _ → ≡.refl;
      qr-cong₂ = λ _ _ → ≡.refl;
      ε-• = ε-•;
      •-ε = •-ε;
      •-• = •-•;
      ql-inner-ε = λ _ _ → ≡.refl;
      qr-outer-ε = λ _ i → t-ε i;
      ql-ql = λ _ _ _ _ → ≡.refl;
      qr-ql = λ _ _ _ _ → ≡.refl;
      qr-qr = λ s v _ i → t-• s v i
    }
    where
      open RawStateLike rawSL
      open IsStateLike isSL
