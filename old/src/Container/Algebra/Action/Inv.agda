{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Action.Inv where

open import Level

import Function as F
open F using (_∘_; Inverseᵇ; Inverseˡ; Inverseʳ)

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
  
  open IsAction isAction public

  field
    inverseˡ : (x : S) → x ⁻¹ · x ≡ ε
    inverseʳ : (x : S) → x · x ⁻¹ ≡ ε
  
  instance
    isGroup : IsGroup _≡_ _·_ ε _⁻¹
    isGroup = record {
        isMonoid = isMonoid;
        ⁻¹-cong = ≡.cong _⁻¹;
        inverse = Prod._,_ inverseˡ inverseʳ
      }

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

module standardize {Con : Container s p} (originalActionInv : ActionInv Con) (uip : UIP (Shape Con)) where
  open ContainerUtil Con
  module original =  ActionInv originalActionInv
  open original hiding (action; isAction; rawAction)
  open Action-properties (original.action)
  
  import Data.Container.Morphism as CM
  open import Container.Morphism.Equality
  open import Container.Morphism.Iso

  open IsEquivalence {{...}}

  Std : Container s p
  Std = S ▷ F.const (P ε)

  iso : Con ⇔ Std
  iso = record {
      to = F.id ▷ λ {x} → σ x;
      from = F.id ▷ λ {x} → σ⁻¹ x;
      to-from = mk≈ (λ _ → ≡.refl) σ-invˡ;
      from-to = mk≈ (λ _ → ≡.refl) σ-invʳ
    }
    where
      ε≡xx⁻¹ : {x : S} → ε ≡ x · x ⁻¹
      ε≡xx⁻¹ {x} = ≡.sym (inverseʳ x)

      x≡εx : {x : S} → x ≡ ε · x
      x≡εx {x} = ≡.sym (identityˡ x) 

      σ : (x : S) → P ε → P x
      σ x = ϕleft {x} {_} ∘ [ ε≡xx⁻¹ ]
      
      σ⁻¹ : (x : S) → P x → P ε
      σ⁻¹ x = ϕleft {ε} {x} ∘ [ x≡εx ]

      σ-invˡ : (x : S) (p₀ : P ε) → σ⁻¹ x (σ x p₀) ≡ p₀
      σ-invˡ x p₀ = begin
          (ϕleft ∘ [ x≡εx ] ∘ ϕleft ∘ [ ε≡xx⁻¹ {x} ]) p₀
        ≡⟨ ≡.cong ϕleft (ϕleft-≡-natural x≡εx ≡.refl ([ ε≡xx⁻¹ {x} ] p₀)) ⟩
          (ϕleft ∘ ϕleft ∘ [ ≡.cong₂ _·_ x≡εx ≡.refl ] ∘ [ ε≡xx⁻¹ ]) p₀
        ≡⟨ ϕleft-homo ε x (x ⁻¹) _ ⟩
          (ϕleft ∘ [ assoc ε x (x ⁻¹) ] ∘ [ ≡.cong₂ _·_ x≡εx ≡.refl ] ∘ [ ε≡xx⁻¹ ]) p₀
        ≡⟨ ϕleft-id-with (inverseʳ x) _ ⟩
          ([ ≡.cong (ε ·_) (inverseʳ x) ⨾ identityʳ ε ]
             ∘ [ assoc ε x (x ⁻¹) ]
             ∘ [ ≡.cong₂ _·_ x≡εx ≡.refl ]
             ∘ [ ε≡xx⁻¹ ]) p₀
        ≡⟨ ≡.subst-subst (assoc ε x (x ⁻¹)) ⨾
           ≡.subst-subst (≡.cong₂ _·_ x≡εx ≡.refl) ⨾
           ≡.subst-subst ε≡xx⁻¹ ⟩
          [ ε≡xx⁻¹ ⨾ ≡.cong₂ _·_ x≡εx ≡.refl ⨾ assoc ε x (x ⁻¹) ⨾ ≡.cong (ε ·_) (inverseʳ x) ⨾ identityʳ ε ]
            p₀
        ≡⟨ ≡.cong (λ eq → [ eq ] p₀) (uip _ ≡.refl) ⟩
          [ ≡.refl ] p₀
        ≡⟨⟩
          p₀
        ∎
        where open ≡.≡-Reasoning

      σ-invʳ : (x : S) (p : P x) → σ x (σ⁻¹ x p) ≡ p
      σ-invʳ x p = begin
          (ϕleft ∘ [ ε≡xx⁻¹ {x} ] ∘ ϕleft ∘ [ x≡εx ]) p
        ≡⟨ ≡.cong ϕleft (ϕleft-≡-natural (ε≡xx⁻¹ {x}) ≡.refl _) ⟩
          (ϕleft ∘ ϕleft ∘ [ ≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl ] ∘ [ x≡εx ]) p
        ≡⟨ ϕleft-homo x (x ⁻¹) x _ ⟩
          (ϕleft ∘ [ assoc x (x ⁻¹) x ] ∘ [ ≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl ] ∘ [ x≡εx ]) p
        ≡⟨ ϕleft-id-with (inverseˡ x) _ ⟩
          ([ ≡.cong (x ·_) (inverseˡ x) ⨾ identityʳ x ]
             ∘ [ assoc x (x ⁻¹) x ]
             ∘ [ ≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl ]
             ∘ [ x≡εx ]) p
        ≡⟨ ≡.subst-subst (assoc x (x ⁻¹) x) ⨾
           ≡.subst-subst (≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl) ⨾
           ≡.subst-subst x≡εx ⟩
          [ x≡εx ⨾ ≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl ⨾ assoc x (x ⁻¹) x ⨾ ≡.cong (x ·_) (inverseˡ x) ⨾ identityʳ x ]
            p
        ≡⟨ ≡.cong (λ eq → [ eq ] p) (uip _ ≡.refl) ⟩
          [ ≡.refl ] p
        ≡⟨⟩
          p
        ∎
        where open ≡.≡-Reasoning

  import Container.Algebra.Action.Morphism as ActionMorphism

  actionStd : Action Std
  actionStd = ActionMorphism.transfer iso (original.action)

  open import Algebra.Properties.Group (group)
    using (⁻¹-anti-homo-∙)
  
  std-left : S → S → P ε → P ε
  std-left x y = actionStd .Action.ϕleft {x} {y}

  std-right : S → S → P ε → P ε
  std-right x y = actionStd .Action.ϕright {x} {y}

  std-right' : S → P ε → P ε
  std-right' x =
      ϕleft {ε} {x ⁻¹} ∘ [ identityˡ (x ⁻¹) ]'
    ∘ ϕright {x} {x ⁻¹} ∘ [ inverseʳ x ]'
  
  std-left≗id : (x y : S) → std-left x y ≗ F.id
  std-left≗id x y p = begin
      std-left x y p
    ≡⟨⟩
      (ϕleft
        ∘ [ identityˡ x ]'
        ∘ ϕleft ∘ ϕleft
        ∘ [ eq1 ]) p
    ≡⟨ ≡.cong (ϕleft ∘ [ identityˡ x ]') (ϕleft-homo x y ((x · y) ⁻¹) _) ⟩
      (ϕleft
        ∘ [ identityˡ x ]'
        ∘ ϕleft ∘ [ eq2 ] ∘ [ eq1 ]) p
    ≡⟨ ≡.cong ϕleft (ϕleft-≡-natural (≡.sym (identityˡ x)) ≡.refl _) ⟩
      (ϕleft ∘ ϕleft
        ∘ [ eq3 ] ∘ [ eq2 ] ∘ [ eq1 ]) p
    ≡⟨ ϕleft-homo ε x (y · (x · y) ⁻¹) _ ⟩
      (ϕleft ∘ [ eq4 ] ∘ [ eq3 ] ∘ [ eq2 ] ∘ [ eq1 ]) p
    ≡⟨ ϕleft-id-with eq5 _ ⟩
      ([ eq5' ]
         ∘ [ eq4 ] ∘ [ eq3 ] ∘ [ eq2 ] ∘ [ eq1 ]) p
    ≡⟨ ≡.subst-subst eq4 ⨾
       ≡.subst-subst eq3 ⨾
       ≡.subst-subst eq2 ⨾
       ≡.subst-subst eq1
    ⟩
      [ eq1 ⨾ eq2 ⨾ eq3 ⨾ eq4 ⨾ eq5' ] p
    ≡⟨ ≡.cong (λ eq → [ eq ] p) (uip _ _) ⟩
      p
    ∎
    where
      open ≡.≡-Reasoning

      eq1 : ε ≡ (x · y) · (x · y) ⁻¹
      eq1 = ≡.sym (inverseʳ _)

      eq2 : (x · y) · (x · y) ⁻¹ ≡ x · (y · (x · y) ⁻¹)
      eq2 = assoc _ _ _

      eq3 : x · (y · (x · y) ⁻¹) ≡ (ε · x) · (y · (x · y) ⁻¹)
      eq3 = ≡.cong₂ _·_ (≡.sym (identityˡ x)) ≡.refl

      eq4 : (ε · x) · (y · (x · y) ⁻¹) ≡ ε · (x · (y · (x · y) ⁻¹))
      eq4 = assoc _ _ _

      eq5 : x · (y · (x · y) ⁻¹) ≡ ε
      eq5 = ≡.sym (assoc _ _ _) ⨾ inverseʳ _

      eq5' : ε · (x · (y · (x · y) ⁻¹)) ≡ ε
      eq5' = ≡.cong (ε ·_) eq5 ⨾ identityʳ ε
  
  std-right≗std-right' : (x y : S) → std-right x y ≗ std-right' x
  std-right≗std-right' x y p = main
    where
      eq-y-cancel : y · (x · y) ⁻¹ ≡ x ⁻¹
      eq-y-cancel = begin
          y · (x · y) ⁻¹
        ≡⟨ ≡.cong (y ·_) (⁻¹-anti-homo-∙ x y) ⟩
          y · (y ⁻¹ · x ⁻¹)
        ≡⟨ assoc _ _ _ ⟨
          (y · y ⁻¹) · x ⁻¹
        ≡⟨ ≡.cong (_· x ⁻¹) (inverseʳ y) ⟩
          ε · x ⁻¹
        ≡⟨ identityˡ _ ⟩
          x ⁻¹
        ∎
        where open ≡.≡-Reasoning
      
      ϕleft-normalize :
        ϕleft ∘ [ identityˡ y ]' ∘ ϕleft ∘ [ eq-y-cancel ]'
          ≗
        ϕleft ∘ [ identityˡ (x ⁻¹) ]'
      ϕleft-normalize p = begin
          (ϕleft ∘ [ identityˡ y ]' ∘ ϕleft ∘ [ eq-y-cancel ]') p
        ≡⟨ ≡.cong ϕleft (ϕleft-≡-natural (≡.sym (identityˡ y)) ≡.refl _) ⟩
          (ϕleft ∘ ϕleft
            ∘ [ ≡.cong₂ _·_ (≡.sym (identityˡ y)) ≡.refl ]
            ∘ [ eq-y-cancel ]') p
        ≡⟨ ϕleft-homo _ _ _ _ ⟩
          (ϕleft
            ∘ [ assoc _ _ _ ]
            ∘ [ ≡.cong₂ _·_ (≡.sym (identityˡ y)) ≡.refl ]
            ∘ [ eq-y-cancel ]') p
        ≡⟨ ϕleft-≡-natural ≡.refl eq-y-cancel _ ⟩
          (ϕleft
            ∘ [ ≡.cong₂ _·_ ≡.refl eq-y-cancel ]
            ∘ [ assoc _ _ _ ]
            ∘ [ ≡.cong₂ _·_ (≡.sym (identityˡ y)) ≡.refl ]
            ∘ [ eq-y-cancel ]') p
        ≡⟨ ≡.cong ϕleft (
            ≡.subst-subst (assoc _ _ _) ⨾
            ≡.subst-subst (≡.cong₂ _·_ (≡.sym (identityˡ y)) ≡.refl) ⨾
            ≡.subst-subst (≡.sym eq-y-cancel)
        ) ⟩
          (ϕleft
            ∘ [ ≡.sym eq-y-cancel ⨾
                ≡.cong₂ _·_ (≡.sym (identityˡ y)) ≡.refl ⨾
                assoc _ _ _ ⨾
                ≡.cong₂ _·_ ≡.refl eq-y-cancel ]) p
        ≡⟨ ≡.cong (λ eq → ϕleft ([ eq ] p)) (uip _ _) ⟩
          (ϕleft ∘ [ identityˡ (x ⁻¹) ]') p
        ∎
        where open ≡.≡-Reasoning
      
      ϕright-normalize :
        [ eq-y-cancel ] ∘ ϕright {x} {y · (x · y) ⁻¹}
          ∘ [ assoc _ _ _ ] ∘ [ inverseʳ (x · y) ]'
          ≗
        ϕright {x} {x ⁻¹} ∘ [ inverseʳ x ]'
      ϕright-normalize p = begin
          ([ eq-y-cancel ] ∘ ϕright {x} {y · (x · y) ⁻¹}
            ∘ [ assoc _ _ _ ] ∘ [ inverseʳ (x · y) ]') p
        ≡⟨ ϕright-≡-natural ≡.refl eq-y-cancel _ ⟩
          (ϕright
            ∘ [ ≡.cong₂ _·_ ≡.refl eq-y-cancel ]
            ∘ [ assoc _ _ _ ] ∘ [ inverseʳ (x · y) ]') p
        ≡⟨ ≡.cong ϕright (
            ≡.subst-subst (assoc _ _ _) ⨾
            ≡.subst-subst (≡.sym (inverseʳ (x · y)))
        ) ⟩
          (ϕright
            ∘ [ ≡.sym (inverseʳ (x · y)) ⨾
                assoc _ _ _ ⨾
                ≡.cong₂ _·_ ≡.refl eq-y-cancel ]) p
        ≡⟨ ≡.cong (λ eq → ϕright ([ eq ] p)) (uip _ _) ⟩
          (ϕright ∘ [ inverseʳ x ]') p
        ∎
        where open ≡.≡-Reasoning

      main : std-right x y p ≡ std-right' x p
      main = begin
          std-right x y p
        ≡⟨⟩
          (ϕleft ∘ [ identityˡ y ]'
            ∘ ϕright ∘ ϕleft ∘ [ inverseʳ (x · y) ]') p
        ≡⟨ ≡.cong (ϕleft ∘ [ identityˡ y ]') (ϕinterchange _ _ _ _) ⟩
          (ϕleft ∘ [ identityˡ y ]'
            ∘ ϕleft ∘ ϕright
            ∘ [ assoc _ _ _ ] ∘ [ inverseʳ (x · y) ]') p
        ≡⟨ ≡.cong (ϕleft ∘ [ identityˡ y ]' ∘ ϕleft) ([]'-cancel eq-y-cancel _) ⟨
          (ϕleft ∘ [ identityˡ y ]'
            ∘ ϕleft
            ∘ [ eq-y-cancel ]' ∘ [ eq-y-cancel ]
            ∘ ϕright
            ∘ [ assoc _ _ _ ] ∘ [ inverseʳ (x · y) ]') p
        ≡⟨ ϕleft-normalize _ ⟩
          (ϕleft ∘ [ identityˡ (x ⁻¹) ]'
            ∘ [ eq-y-cancel ]
            ∘ ϕright
            ∘ [ assoc _ _ _ ] ∘ [ inverseʳ (x · y) ]') p
        ≡⟨ ≡.cong (ϕleft ∘ [ identityˡ (x ⁻¹) ]') (ϕright-normalize _) ⟩
          (ϕleft ∘ [ identityˡ (x ⁻¹) ]'
            ∘ ϕright {x} {x ⁻¹} ∘ [ inverseʳ x ]') p
        ≡⟨⟩
          std-right' x p
        ∎
        where open ≡.≡-Reasoning