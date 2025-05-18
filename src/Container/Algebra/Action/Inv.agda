{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Action.Inv where

open import Level

import Function as F
open F using (Inverseᵇ; Inverseˡ; Inverseʳ)

import Data.Product as Prod
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_)

open import Axiom.UniquenessOfIdentityProofs using (UIP)

open import Data.Container.Core
open import Algebra
  using (Op₁; Op₂; RawMonoid; IsMonoid; Monoid; RawGroup; IsGroup; Group)

open import Container.Algebra.Action

private
  variable
    a b c s p e : Level

record RawActionInv (Con : Container s p) : Set (s ⊔ p) where
  field
    rawAction : RawAction Con
    _⁻¹ : Op₁ (Shape Con)
  
  open RawAction rawAction public

  instance
    rawGroup : RawGroup s s
    rawGroup = record { Carrier = S; _≈_ = _≡_; _∙_ = _·_; ε = ε; _⁻¹ = _⁻¹ }

record IsActionInv (Con : Container s p) (raw : RawActionInv Con) : Set (s ⊔ p) where
  open RawActionInv raw
  
  field
    instance
      isAction : IsAction Con rawAction
    instance
      isGroup : IsGroup _≡_ _·_ ε _⁻¹

  open IsAction isAction public
  open IsGroup isGroup using (inverseˡ; inverseʳ) public

record ActionInv (Con : Container s p) : Set (s ⊔ p) where
  field
    rawActionInv : RawActionInv Con
    isActionInv : IsActionInv Con rawActionInv
  
  open RawActionInv rawActionInv public
  open IsActionInv isActionInv public

  action : Action Con
  action = record { rawAction = rawAction; isAction = isAction }

module WithUIP (Con : Container s p) (uip : UIP (Shape Con)) where
  open Container Con renaming (Shape to S; Position to P)
  
  subst-elim : ∀ {x : S} (eq : x ≡ x) (p : P x)
    → ≡.subst P eq p ≡ p
  subst-elim eq p = ≡.cong (λ eq' → ≡.subst P eq' p) (uip eq ≡.refl)

private
  subst-const : ∀ {a b} {A : Set a} {x y : A} (B : Set b) (x≡y : x ≡ y)
    → (p : B) → ≡.subst (F.const B) x≡y p ≡ p
  subst-const _ ≡.refl _ = ≡.refl

module util {Con : Container s p} (action : Action Con) where
  open Action action
  ϕleft-≡-natural : ∀ {x y : S}
    → (x≡y : x ≡ y) (z : S) {p : P (x · z)}
    → lift≡ x≡y (ϕleft p) ≡ ϕleft (lift≡ (≡.cong (_· z) x≡y) p)
  ϕleft-≡-natural ≡.refl _ = ≡.refl

  indir-identityʳ : ∀ (x : S) {y : S} (eq : y ≡ ε)
    → x · y ≡ x
  indir-identityʳ x eq = ≡.trans (≡.cong (x ·_) eq) (identityʳ x)

  ϕleft-id' : ∀ {x : S} {y : S} (eq : y ≡ ε) (p : P (x · y))
    → ϕleft p ≡ lift≡ (indir-identityʳ x eq) p
  ϕleft-id' ≡.refl p = ϕleft-id _ p

module reformulation {Con : Container s p} (actionInv : ActionInv Con) where
  open ActionInv actionInv
  
  open import Data.Container.Morphism as CM
    using (_∘_; id)
  open import Container.Morphism.Equality

  -- synonym
  inv : S → S
  inv = _⁻¹

  -- Action laws regarding ϕleft, ϕright are
  -- decribed using Container morphisms `actLeft, actRight` 

  actLeft : S → Con ⇒ Con
  actLeft x .shape = (x ·_)
  actLeft x .position = ϕright
  
  actRight : S → Con ⇒ Con
  actRight x .shape = (_· x)
  actRight x .position = ϕleft

  -- Properties of actLeft, actRight

  left-ε : actLeft ε ≈ id Con
  left-ε = mk≈ identityˡ ϕright-id

  right-ε : actRight ε ≈ id Con
  right-ε = mk≈ identityʳ ϕleft-id

  left-· : (x y : S) → actLeft (x · y) ≈ actLeft x ∘ actLeft y
  left-· x y = mk≈ (λ z → assoc x y z) (λ z → ϕright-homo x y z)

  right-· : (y z : S) → actRight z ∘ actRight y ≈ actRight (y · z) 
  right-· y z = mk≈ (λ x → assoc x y z) (λ x → ϕleft-homo x y z)

  left-right-comm : (x z : S)
    → actRight z ∘ actLeft x ≈ actLeft x ∘ actRight z
  left-right-comm x z = mk≈ (λ y → assoc x y z) (λ y → ϕinterchange x y z)

  -- actLeft and actRight have inverses

  open IsEquivalence {{...}}

  left-inverse-l : (x : S) → actLeft (inv x) ∘ actLeft x ≈ CM.id Con
  left-inverse-l x =
    begin
      actLeft (inv x) ∘ actLeft x
    ≈⟨ left-· (inv x) x ⟨
      actLeft (inv x · x)
    ≈⟨ reflexive (≡.cong actLeft (inverseˡ x)) ⟩
      actLeft ε
    ≈⟨ left-ε ⟩
      CM.id Con
    ∎
    where open Reasoning ≈-setoid
  
  left-inverse-r : (x : S) → actLeft x ∘ actLeft (inv x) ≈ CM.id Con
  left-inverse-r x =
    begin
      actLeft x ∘ actLeft (inv x)
    ≈⟨ left-· x (inv x) ⟨
      actLeft (x · inv x)
    ≈⟨ reflexive (≡.cong actLeft (inverseʳ x)) ⟩
      actLeft ε
    ≈⟨ left-ε ⟩
      CM.id Con
    ∎
    where open Reasoning ≈-setoid

  right-inverse-l : (x : S) → actRight (inv x) ∘ actRight x ≈ CM.id Con
  right-inverse-l x =
    begin
      actRight (inv x) ∘ actRight x
    ≈⟨ right-· x (inv x) ⟩
      actRight (x · inv x)
    ≈⟨ reflexive (≡.cong actRight (inverseʳ x)) ⟩
      actRight ε
    ≈⟨ right-ε ⟩
      CM.id Con
    ∎
    where open Reasoning ≈-setoid
  
  right-inverse-r : (x : S) → actRight x ∘ actRight (inv x) ≈ CM.id Con
  right-inverse-r x =
    begin
      actRight x ∘ actRight (inv x)
    ≈⟨ right-· (inv x) x ⟩
      actRight (inv x · x)
    ≈⟨ reflexive (≡.cong actRight (inverseˡ x)) ⟩
      actRight ε
    ≈⟨ right-ε ⟩
      CM.id Con
    ∎
    where open Reasoning ≈-setoid
  
module standardize {Con : Container s p} (actionInv : ActionInv Con) (uip : UIP (Shape Con)) where
  open ActionInv actionInv
  
  open import Data.Container.Morphism as CM
    using (_∘_; id)
  open import Container.Morphism.Equality

  open util action
  open WithUIP Con uip using (subst-elim)

  -- synonym
  inv : S → S
  inv = _⁻¹

  R : Container s p
  R .Shape = S
  R .Position s = P (s · inv s)

  Con⇒R : Con ⇒ R
  Con⇒R .shape = F.id
  Con⇒R .position = ϕleft

  -- reg ≗ id
  reg : S → S
  reg x = (x · inv x) · x

  regular : (x : S) → reg x ≡ x
  regular x = ≡.trans (≡.cong (_· x) (inverseʳ x)) (identityˡ x)

  R⇒Con : R ⇒ Con
  R⇒Con .shape = reg
  R⇒Con .position = ϕleft
  
  R⇔Con-right : R⇒Con ∘ Con⇒R ≈ id Con
  R⇔Con-right = mk≈ regular eqP
    where
      eqP : ∀ (x : S) (p : P (reg x))
        → ϕleft (ϕleft p) ≡ lift≡ (regular x) p
      eqP x p = begin
            ϕleft (ϕleft p)
          ≡⟨ ϕleft-homo _ _ _ p ⟩
            ϕleft (lift≡ eq1 p)
          ≡⟨ ϕleft-id' (inverseˡ x) (lift≡ eq1 p) ⟩
            lift≡ eq2 (lift≡ eq1 p)
          ≡⟨ ≡.subst-subst eq1 ⟩
            lift≡ (≡.trans eq1 eq2) p
          ≡⟨ ≡.cong (λ eq → lift≡ eq p) (uip _ (regular x)) ⟩
            lift≡ (regular x) p
          ∎
        where
          open ≡.≡-Reasoning

          eq1 : reg x ≡ x · (inv x · x)
          eq1 = assoc _ _ _

          eq2 : x · (inv x · x) ≡ x
          eq2 = indir-identityʳ x (inverseˡ x)
  
  R⇔Con-left : Con⇒R ∘ R⇒Con ≈ id R
  R⇔Con-left = mk≈ regular eqP
    where
      eqP : ∀ (x : S)
        (p : P (reg x · inv (reg x)))
        → ϕleft (ϕleft p) ≡ ≡.subst (λ s → P (s · inv s)) (regular x) p
      eqP x p = begin
            ϕleft (ϕleft p)
          ≡⟨ ϕleft-homo _ _ _ p ⟩
            ϕleft (lift≡ eq1 p)
          ≡⟨ ϕleft-id' xy⁻¹≡ε (lift≡ eq1 p) ⟩
            lift≡ eq2 (lift≡ eq1 p)
          ≡⟨ ≡.subst-subst eq1 ⟩
            lift≡ (≡.trans eq1 eq2) p
          ≡⟨ ≡.cong (λ eq → lift≡ eq p) (uip _ eqS') ⟩
            lift≡ eqS' p
          ≡⟨ ≡.subst-∘ (regular x) ⟨
            ≡.subst (λ s → P (s · inv s)) (regular x) p
          ∎
        where
          open ≡.≡-Reasoning

          y : S
          y = reg x
          
          eqS' : y · inv y ≡ x · inv x
          eqS' = ≡.cong (λ s → s · inv s) (regular x)

          xy⁻¹≡ε : x · inv y ≡ ε
          xy⁻¹≡ε = ≡.trans (≡.cong (λ y → x · inv y) (regular x)) (inverseʳ x)

          eq1 : y · inv y ≡ (x · inv x) · (x · inv y)
          eq1 = assoc _ _ _

          eq2 : (x · inv x) · (x · inv y) ≡ x · inv x
          eq2 = indir-identityʳ (x · inv x) xy⁻¹≡ε
