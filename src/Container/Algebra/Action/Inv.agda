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
    renaming (isEquivalence to ≡-isEquivalence)

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

module standardize {Con : Container s p} (originalActionInv : ActionInv Con) (uip : UIP (Shape Con)) where
  open ContainerUtil Con
  module original =  ActionInv originalActionInv
  open original hiding (action; isAction; rawAction)
  open Action-properties (original.action)
  
  open import Data.Container.Morphism as CM
    using (_∘_; id)
  open import Container.Morphism.Equality
  open import Container.Morphism.Iso

  open WithUIP Con uip using (subst-elim)

  open IsEquivalence {{...}}

  private
    -- Auxiliary definitions
    inv : S → S
    inv = _⁻¹

  Std : Container s p
  Std = S ▷ F.const (P ε)

  module StdAction where
    open import Algebra.Properties.Group (group)
      using (⁻¹-anti-homo-∙; ε⁻¹≈ε)
    
    private
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
      
      ψright-homo⁻¹ : ∀ (x y : S) (q : P ε) → ψright y (ψright x q) ≡ ψright (x · y) q
      ψright-homo⁻¹ x y q =
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
    
    rawAction : RawAction Std
    rawAction = record {
        ε = ε;
        _·_ = _·_;
        ϕleft = λ p → p;
        ϕright = λ {x} {_} → ψright x
      }

    isAction : IsAction Std rawAction
    isAction = record {
        isMonoid = isMonoid;
        ϕleft-id = λ _ → wrap refl;
        ϕright-id = λ _ → wrap ψright-id;
        ϕleft-homo = λ _ _ _ → wrap refl;
        ϕright-homo = λ x y _ → wrap (sym (ψright-homo⁻¹ x y));
        ϕinterchange = λ _ _ _ → wrap refl 
      }
      where
        wrap : ∀ {x y : S} {eq : x ≡ y} {f g : P ε → P ε} → f ≗ g → f ≗ g F.∘ ≡.subst (F.const (P ε)) eq
        wrap {eq = ≡.refl} {f = f} {g = g} f≗g = f≗g
    
    action : Action Std
    action = record { isAction = isAction }

  private
    Q : S → Set p
    Q s = P (s · inv s)

    reg : S → S
    reg x = (x · inv x) · x

    regular : (x : S) → reg x ≡ x
    regular x = ≡.cong (_· x) (inverseʳ x) ⨾ identityˡ x

  -- It is easier to show `Con ⇔ R` and `R ⇔ Std`
  -- separately, rather than direct `Con ⇔ Std`.

  R : Container s p
  R = S ▷ Q

  R⇔Std : R ⇔ Std
  R⇔Std = record {
      to = to; from = from;
      to-from = to-from; from-to = from-to
    } where

    to : R ⇒ Std
    to .shape = F.id
    to .position {s = s} = [ inverseʳ s ]'

    from : Std ⇒ R
    from .shape = F.id
    from .position {s = s} = [ inverseʳ s ]

    to-from : to ∘ from ≈ id Std
    to-from = mk≈ refl (λ s → []-cancel (inverseʳ s))
    
    from-to : from ∘ to ≈ id R
    from-to = mk≈ refl (λ s → []'-cancel (inverseʳ s))

  Con⇔R : Con ⇔ R
  Con⇔R = record {
      to = to;
      from = from;
      to-from = to-from;
      from-to = from-to
    } where

    to : Con ⇒ R
    to = F.id ▷ ϕleft

    from : R ⇒ Con
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
    
    to-from : to ∘ from ≈ id R
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

  Con⇒Std : Con ⇒ Std
  Con⇒Std = R⇔Std ._⇔_.to ∘ Con⇔R ._⇔_.to

  -- TODO: Implement this
  -- isActionMorphism : IsActionMorphism original.action StdAction.action Con⇒Std
  -- isActionMorphism = _