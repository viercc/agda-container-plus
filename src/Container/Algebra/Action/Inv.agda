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
  
module standardize {Con : Container s p} (actionInv : ActionInv Con) (uip : UIP (Shape Con)) where
  open ContainerUtil Con
  open ActionInv actionInv
  open Action-properties (action)
  
  open import Data.Container.Morphism as CM
    using (_∘_; id)
  open import Container.Morphism.Equality
  open import Container.Morphism.Iso

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
    ψright-id q =
      begin
        ψright ε q
      ≡⟨⟩
        (ϕmid F.∘′ [ midε ε ]) q
      ≡⟨ ϕmid-id-with ≡.refl ε⁻¹≈ε ([ midε ε ] q) ⟩
       [ ≡.cong₂ _·_ ≡.refl ε⁻¹≈ε ⨾ identity-mid ε ] ([ midε ε ] q)
      ≡⟨ []-trans {eq1 = midε ε} q ⟩
       [ midε ε ⨾ ≡.cong₂ _·_ ≡.refl ε⁻¹≈ε ⨾ identity-mid ε ] q
       -- I might be able to reduce the (eq : ε · ε · ε⁻¹ ≡ ε) to refl in this case,
       -- but I don't bother and use UIP
      ≡⟨ subst-elim _ q ⟩
        q
      ∎
      where
        open ≡.≡-Reasoning
    
    ψright-homo : ∀ (x y : S) (q : P ε) → ψright y (ψright x q) ≡ ψright (x · y) q
    ψright-homo x y q =
      begin
        ψright y (ψright x q)
      ≡⟨⟩
        (ϕmid F.∘′ [ midε y ] F.∘′ ϕmid F.∘′ [ eq1 ]) q
      ≡⟨ ≡.cong ϕmid (ϕmid-≡-natural ≡.refl (midε y) ≡.refl _) ⟩
       (ϕmid F.∘′ ϕmid F.∘′ [ eq2 ] F.∘′ [ eq1 ]) q
      ≡⟨ ≡.cong (ϕmid F.∘′ ϕmid) (≡.subst-subst eq1) ⟩
       (ϕmid F.∘′ ϕmid F.∘′ [ eq1 ⨾ eq2 ]) q
      ≡⟨ ϕmid-mid x y ε (inv y) (inv x) _ ⟩
       (ϕmid F.∘′ [ eq3 ] F.∘′ [ eq1 ⨾ eq2 ]) q
      ≡⟨ ≡.cong ϕmid (≡.subst-subst (eq1 ⨾ eq2)) ⟩
       (ϕmid F.∘′ [ (eq1 ⨾ eq2) ⨾ eq3 ]) q
      ≡⟨ ϕmid-≡-natural ≡.refl ≡.refl (≡.sym (⁻¹-anti-homo-∙ x y)) _ ⟩
       (ϕmid F.∘′ [ eq4 ] F.∘′ [ (eq1 ⨾ eq2) ⨾ eq3 ]) q
      ≡⟨ ≡.cong ϕmid (≡.subst-subst ((eq1 ⨾ eq2) ⨾ eq3)) ⟩
       (ϕmid F.∘′ [ ((eq1 ⨾ eq2) ⨾ eq3) ⨾ eq4 ]) q
      ≡⟨ ≡.cong (λ eq → ϕmid ([ eq ] q)) (uip _ _) ⟩
       (ϕmid F.∘′ [ midε (x · y) ]) q
      ≡⟨⟩
        ψright (x · y) q
      ∎
      where
        open ≡.≡-Reasoning

        eq1 : ε ≡ x · ε · inv x 
        eq1 = midε x

        eq2 : x · ε · inv x ≡ x · (y · ε · inv y) · inv x
        eq2 = ≡.cong₂ _·_ (≡.cong₂ _·_ ≡.refl (midε y)) ≡.refl

        eq3 : x · (y · ε · inv y) · inv x ≡ (x · y) · ε · (inv y · inv x)
        eq3 = assoc-mid x y ε (inv y) (inv x)

        eq4 : (x · y) · ε · (inv y · inv x) ≡ (x · y) · ε · inv (x · y)
        eq4 = ≡.cong₂ _·_ ≡.refl (≡.sym (⁻¹-anti-homo-∙ x y))

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
            ≡⟨ ϕleft-id-with (inverseˡ x) ([ eq1 ] p) ⟩
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
            eq2 = ≡.cong (x ·_) (inverseˡ x) ⨾ identityʳ x
    
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
            ≡⟨ ϕleft-id-with xy⁻¹≡ε ([ eq1 ] p) ⟩
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
