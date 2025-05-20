{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Action.Inv where

open import Level

import Function as F
open F using (Inverseᵇ; Inverseˡ; Inverseʳ)

import Data.Product as Prod
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; _≗_)

open import Axiom.UniquenessOfIdentityProofs using (UIP)

open import Data.Container.Core
open import Algebra
  using (Op₁; Op₂; RawMonoid; IsMonoid; Monoid; RawGroup; IsGroup; Group)

open import Container.Algebra.Action

private
  variable
    a b c s p e : Level

record RawActionInv (Con : Container s p) : Set (s ⊔ p) where
  open ContainerUtil Con using (S; P)

  field
    rawAction : RawAction Con
    _⁻¹ : Op₁ (Shape Con)
  
  open RawAction rawAction public

  instance
    rawGroup : RawGroup s s
    rawGroup = record { Carrier = S; _≈_ = _≡_; _∙_ = _·_; ε = ε; _⁻¹ = _⁻¹ }

record IsActionInv (Con : Container s p) (raw : RawActionInv Con) : Set (s ⊔ p) where
  open ContainerUtil Con using (S; P)
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

  group : Group s s
  group = record { isGroup = isGroup }

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
  open ContainerUtil Con
  open Action action
  ϕleft-≡-natural : ∀ {x y : S}
    → (x≡y : x ≡ y) (z : S)
    → [ x≡y ] F.∘′ ϕleft ≗ ϕleft F.∘′ [ ≡.cong (_· z) x≡y ]
  ϕleft-≡-natural ≡.refl _ _ = ≡.refl

  indir-identityʳ : ∀ (x : S) {y : S} (eq : y ≡ ε)
    → x · y ≡ x
  indir-identityʳ x eq = ≡.trans (≡.cong (x ·_) eq) (identityʳ x)

  ϕleft-id' : ∀ {x : S} {y : S} (eq : y ≡ ε)
    → ϕleft ≗ [ indir-identityʳ x eq ]
  ϕleft-id' ≡.refl = ϕleft-id _

module reformulation {Con : Container s p} (actionInv : ActionInv Con) where
  open ContainerUtil Con using (S; P)
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
  
  left-inverse-Rpre : (x : S) → actLeft x ∘ actLeft (inv x) ≈ CM.id Con
  left-inverse-Rpre x =
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
  
  right-inverse-Rpre : (x : S) → actRight x ∘ actRight (inv x) ≈ CM.id Con
  right-inverse-Rpre x =
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
  open ContainerUtil Con
  open ActionInv actionInv
  
  open import Data.Container.Morphism as CM
    using (_∘_; id)
  open import Container.Morphism.Equality
  open import Container.Morphism.Iso

  open util action
  open WithUIP Con uip using (subst-elim)

  private
    -- Auxiliary definitions
    inv : S → S
    inv = _⁻¹

    Q : S → Set p
    Q s = P (s · inv s)

    reg : S → S
    reg x = (x · inv x) · x

    regular : (x : S) → reg x ≡ x
    regular x = ≡.cong (_· x) (inverseʳ x) ⨾ identityˡ x

  -- It is easier to show `Con ⇔ Rpre` and `Rpre ⇔ R`
  -- separately, rather than direct `Con ⇔ R`.

  Rpre : Container s p
  Rpre = S ▷ Q

  R : Container s p
  R = S ▷ F.const (P ε)

  Rpre⇔R : Rpre ⇔ R
  Rpre⇔R = record {
      to = to; from = from;
      to-from = to-from; from-to = from-to
    } where

    to : Rpre ⇒ R
    to .shape = F.id
    to .position {s = s} = [ inverseʳ s ]'

    from : R ⇒ Rpre
    from .shape = F.id
    from .position {s = s} = [ inverseʳ s ]

    to-from : to ∘ from ≈ id R
    to-from = mk≈ (λ _ → ≡.refl) (λ s → []-cancel (inverseʳ s))
    
    from-to : from ∘ to ≈ id Rpre
    from-to = mk≈ (λ _ → ≡.refl) (λ s → []'-cancel (inverseʳ s))

  module R-action where
    open import Algebra.Properties.Group (group)
      using (⁻¹-anti-homo-∙; ε⁻¹≈ε)

    midε : ∀ (x : S) → ε ≡ (x · ε) · inv x
    midε x = ≡.sym (≡.cong (_· inv x) (identityʳ x) ⨾ inverseʳ x)

    ψright : ∀ (x : S) → P ε → P ε
    ψright x = ϕmid F.∘′ [ midε x ]

    ψright-id : ∀ (q : P ε) → ψright ε q ≡ q
    ψright-id q = begin
      ψright ε q
        ≡⟨⟩
      ϕright (ϕleft ([ midε ε ] q))
        ≡⟨ ≡.cong ϕright (ϕleft-id' ε⁻¹≈ε ([ midε ε ] q)) ⟩
      _
        ≡⟨ _ ⟩
      q
      ∎
      where
        open ≡.≡-Reasoning

  Con⇔Rpre : Con ⇔ Rpre
  Con⇔Rpre = record {
      to = to;
      from = from;
      to-from = to-from;
      from-to = from-to
    } where

    to : Con ⇒ Rpre
    to = F.id ▷ ϕleft

    from : Rpre ⇒ Con
    from = reg ▷ ϕleft
    
    from-to : from ∘ to ≈ id Con
    from-to = mk≈ regular eqP
      where
        eqP : ∀ (x : S) (p : P (reg x))
          → ϕleft (ϕleft p) ≡ [ regular x ] p
        eqP x p = begin
              ϕleft (ϕleft p)
            ≡⟨ ϕleft-homo _ _ _ p ⟩
              ϕleft ([ eq1 ] p)
            ≡⟨ ϕleft-id' (inverseˡ x) ([ eq1 ] p) ⟩
              [ eq2 ] ([ eq1 ] p)
            ≡⟨ ≡.subst-subst eq1 ⟩
              [ eq1 ⨾  eq2 ] p
            ≡⟨ ≡.cong (λ eq → [ eq ] p) (uip _ (regular x)) ⟩
              [ regular x ] p
            ∎
          where
            open ≡.≡-Reasoning

            eq1 : reg x ≡ x · (inv x · x)
            eq1 = assoc _ _ _

            eq2 : x · (inv x · x) ≡ x
            eq2 = indir-identityʳ x (inverseˡ x)
    
    to-from : to ∘ from ≈ id Rpre
    to-from = mk≈ regular eqP
      where
        eqP : ∀ (x : S)
          (p : P (reg x · inv (reg x)))
          → ϕleft (ϕleft p) ≡ ≡.subst Q (regular x) p
        eqP x p = begin
              ϕleft (ϕleft p)
            ≡⟨ ϕleft-homo _ _ _ p ⟩
              ϕleft ([ eq1 ] p)
            ≡⟨ ϕleft-id' xy⁻¹≡ε ([ eq1 ] p) ⟩
              [ eq2 ] ([ eq1 ] p)
            ≡⟨ ≡.subst-subst eq1 ⟩
              [ eq1 ⨾ eq2 ] p
            ≡⟨ ≡.cong (λ eq → [ eq ] p) (uip _ eqS') ⟩
              [ eqS' ] p
            ≡⟨ ≡.subst-∘ (regular x) ⟨
              ≡.subst Q (regular x) p
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
