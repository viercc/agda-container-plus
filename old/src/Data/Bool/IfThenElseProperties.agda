{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base
  using (Bool; true; false; if_then_else_; _∧_; _∨_)
import Data.Bool.Properties as BoolProp

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)

module Data.Bool.IfThenElseProperties
  {a} {A : Set a} where

case-apply : ∀ {b} {B : Set b}
  (cond : Bool) (f g : A → B) {x y : A}
  → (if cond then f else g) (if cond then x else y) ≡ (if cond then f x else g y)
case-apply true  _ _ = ≡.refl
case-apply false _ _ = ≡.refl

case-apply₁ : ∀ {b} {B : Set b}
  (cond : Bool) (f g : A → B) {x : A}
  → (if cond then f else g) x ≡ (if cond then f x else g x)
case-apply₁ true  _ _ = ≡.refl
case-apply₁ false _ _ = ≡.refl

case-apply₂ : ∀ {b} {B : Set b}
  (cond : Bool) (f : A → B) {x y : A}
  → f (if cond then x else y) ≡ (if cond then f x else f y)
case-apply₂ true  _ = ≡.refl
case-apply₂ false _ = ≡.refl

if-dud : ∀ {cond : Bool} {x : A}
  → (if cond then x else x) ≡ x
if-dud {cond = false} = ≡.refl
if-dud {cond = true} = ≡.refl

if-and : ∀ (cond₁ cond₂ : Bool) {x y : A}
  → (if cond₁ then (if cond₂ then x else y) else y) ≡ (if (cond₁ ∧ cond₂) then x else y)
if-and false _ = ≡.refl
if-and true false = ≡.refl
if-and true true = ≡.refl

if-then-if : ∀ (cond : Bool) {x y z : A}
  → (if cond then (if cond then x else y) else z) ≡ (if cond then x else z)
if-then-if false = ≡.refl
if-then-if true = ≡.refl

if-else-if : ∀ (cond : Bool) {x y z : A}
  → (if cond then x else (if cond then y else z)) ≡ (if cond then x else z)
if-else-if false = ≡.refl
if-else-if true = ≡.refl