{-# OPTIONS --without-K --safe #-}

open import Data.Empty

open import Data.Bool.Base
  using (Bool; true; false; if_then_else_; _∧_; _∨_)
import Data.Bool.IfThenElseProperties

open import Relation.Nullary
  using (Dec; does; yes; no; ⌊_⌋)
open import Relation.Binary
  using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≢_)

module Relation.Binary.DecidableEquality.Util
  {p} {I : Set p}
  (_≟_ : DecidableEquality I) where

infix 4 _==_

_==_ : I → I → Bool
_==_ x y = ⌊ x ≟ y ⌋

dec-eq : ∀ {i j : I} → (i ≡ j) → (i == j) ≡ true
dec-eq {i} {j} i≡j with i ≟ j
... | yes _ = ≡.refl
... | no i≢j = ⊥-elim (i≢j i≡j)

dec-neq : ∀ {i j : I} → (i ≢ j) → (i == j) ≡ false
dec-neq {i} {j} i≢j with i ≟ j
... | yes i≡j = ⊥-elim (i≢j i≡j)
... | no _ = ≡.refl

dec-refl : ∀ {i : I} → (i == i) ≡ true
dec-refl = dec-eq ≡.refl

elim-if-refl : ∀ {i : I} {a} {A : Set a} {x y : A}
  → (if i == i then x else y) ≡ x
elim-if-refl = ≡.cong (if_then _ else _) dec-refl

rewrite-under-if : ∀ (i j : I) {a} {A : Set a} {x₁ x₂ y : A}
  → (i ≡ j → x₁ ≡ x₂) → (if i == j then x₁ else y) ≡ (if i == j then x₂ else y)
rewrite-under-if i j rewriter with i ≟ j
... | yes i≡j = rewriter i≡j
... | no _ = ≡.refl

rewrite-under-if-else : ∀ (i j : I) {a}
    {A : Set a} {x₁ x₂ y₁ y₂ : A}
  → (i ≡ j → x₁ ≡ x₂)
  → (i ≢ j → y₁ ≡ y₂)
  → (if i == j then x₁ else y₁) ≡ (if i == j then x₂ else y₂)
rewrite-under-if-else i j rewriter-x rewriter-y with i ≟ j
... | yes i≡j = rewriter-x i≡j
... | no i≢j = rewriter-y i≢j
