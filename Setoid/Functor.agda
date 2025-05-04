{-# OPTIONS --without-K --safe #-}

-- | Functor on Setoids (rather than Set)
module Setoid.Functor where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality.Properties
  renaming (setoid to ≡-setoid)
import Relation.Binary.PropositionalEquality.Core as P

import Function.Base as F
open import Function using (Func)
import Function.Construct.Identity as Id
import Function.Construct.Composition as Comp

private
  variable
    c₁ l₁ c₂ l₂ : Level

infix 2 _≗_

-- Pointwise equivalence between Func
data _≗_ {A B : Setoid c₁ l₁} : Rel (Func A B) (c₁ ⊔ l₁) where
  pweq : (f g : Func A B) → (∀ a → Setoid._≈_ B (Func.to f a) (Func.to g a)) → f ≗ g

≗-refl : {A B : Setoid c₁ l₁} {f : Func A B} → f ≗ f
≗-refl {B = B} {f = f} = pweq f f (λ _ → SB.refl)
  where
    module SB = Setoid B

≗-sym : {A B : Setoid c₁ l₁} {f g : Func A B} → f ≗ g → g ≗ f
≗-sym {B = B} (pweq f g f≗g) = pweq g f (λ a → SB.sym (f≗g a))
  where
    module SB = Setoid B

≗-trans : {A B : Setoid c₁ l₁} {f g h : Func A B} → f ≗ g → g ≗ h → f ≗ h
≗-trans {A = A} {B = B} (pweq f _ f≗g) (pweq _ h g≗h) = pweq f h f≗h
  where
    module SB = Setoid B
    f≗h : (a : Setoid.Carrier A) → SB._≈_ (Func.to f a) (Func.to h a)
    f≗h a = SB.trans (f≗g a) (g≗h a)

≗-isEquivalence : {A B : Setoid c₁ l₁} → IsEquivalence (_≗_ {A = A} {B = B})
≗-isEquivalence = record { refl = ≗-refl; sym = ≗-sym; trans = ≗-trans }

-- TODO : IsEquivalence _≗_

id : (A : Setoid c₁ l₁) → Func A A
id = Id.function

infixr 9 _∘_

_∘_ : {A B C : Setoid c₁ l₁} → Func B C → Func A B → Func A C
_∘_ f g = Comp.function g f

record Functor (F : Setoid c₁ l₁ → Setoid c₂ l₂)
    : Set (suc (c₁ ⊔ l₁) ⊔ c₂ ⊔ l₂) where
  field
    fmap : {A B : Setoid c₁ l₁} → Func A B → Func (F A) (F B)
    fmap-resp-≗ : {A B : Setoid c₁ l₁}
      → {f g : Func A B}
      → (f ≗ g) → (fmap f ≗ fmap g)
    
    fmap-id : {A : Setoid c₁ l₁}
      → fmap (id A) ≗ id (F A)
    fmap-comp : {A B C : Setoid c₁ l₁}
      → (f : Func B C) → (g : Func A B)
      → fmap (f ∘ g) ≗ fmap f ∘ fmap g

record Functor' (F : Set c₁ → Setoid c₂ l₂)
    : Set (suc c₁ ⊔ c₂ ⊔ l₂) where
  field
    fmap' : {A B : Set c₁} → (A → B) → Func (F A) (F B)
    
    fmap'-id : {A : Set c₁}
      → fmap' F.id ≗ id (F A)
    
    fmap'-comp : {A B C : Set c₁}
      → (f : B → C) → (g : A → B)
      → fmap' (F._∘_ f g) ≗ fmap' f ∘ fmap' g

wrapFunc : ∀ {c₁} {A B : Set c₁} → (A → B) → Func (≡-setoid A) (≡-setoid B)
wrapFunc f = record { to = f; cong = P.cong f }

-- lemma
wrapId≗id : ∀ {A : Set c₁} → wrapFunc F.id ≗ id (≡-setoid A)
wrapId≗id {A = A} = pweq (wrapFunc F.id) (id (≡-setoid A)) (λ x → P.refl)

wrapComp≗comp : ∀ {A B C : Set c₁}
  → (f : B → C) → (g : A → B)
  → wrapFunc (f F.∘ g) ≗ wrapFunc f ∘ wrapFunc g
wrapComp≗comp {_} {A} {B} {C} f g = pweq lhs rhs eq
  where
    lhs = wrapFunc (f F.∘ g)
    rhs = wrapFunc f ∘ wrapFunc g

    eq : ∀ (x : A) → Func.to lhs x P.≡ Func.to rhs x
    eq _ = P.refl

Functor-to-Functor' : ∀ {c} {F : Setoid c c → Setoid c₂ l₂} → Functor F → Functor' (F F.∘ ≡-setoid)
Functor-to-Functor' {c = c} {F = F} functorF = record{
      fmap' = fmap'; fmap'-id = fmap'-id; fmap'-comp = fmap'-comp
    }
  where
    open Functor functorF

    fmap' : {A B : Set c} → (A → B) → Func (F (≡-setoid A)) (F (≡-setoid B))
    fmap' f = fmap (wrapFunc f)

    fmap'-id : {A : Set c} → fmap' F.id ≗ id (F (≡-setoid A))
    fmap'-id {A} = ≗-trans
      (fmap-resp-≗ (wrapId≗id {A = A}))
      fmap-id

    fmap'-comp : {A B C : Set c}
      → (f : B → C) → (g : A → B)
      → fmap' (F._∘_ f g) ≗ fmap' f ∘ fmap' g
    fmap'-comp {A} {B} {C} f g = ≗-trans
      (fmap-resp-≗ (wrapComp≗comp f g))
      (fmap-comp (wrapFunc f) (wrapFunc g))