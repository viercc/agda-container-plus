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
  
  open import Data.Container.Morphism as CM
    using (_∘_; id)
  open import Container.Morphism.Equality
  open import Container.Morphism.Iso

  open IsEquivalence {{...}}

  private
    -- Auxiliary definitions
    inv : S → S
    inv = _⁻¹

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
      σ x = ϕleft {x} {_} F.∘ [ ε≡xx⁻¹ ]
      
      σ⁻¹ : (x : S) → P x → P ε
      σ⁻¹ x = ϕleft {ε} {x} F.∘ [ x≡εx ]

      σ-invˡ : (x : S) (p₀ : P ε) → σ⁻¹ x (σ x p₀) ≡ p₀
      σ-invˡ x p₀ = begin
          (ϕleft F.∘ [ x≡εx ] F.∘ ϕleft F.∘ [ ε≡xx⁻¹ {x} ]) p₀
        ≡⟨ ≡.cong ϕleft (ϕleft-≡-natural x≡εx ≡.refl ([ ε≡xx⁻¹ {x} ] p₀)) ⟩
          (ϕleft F.∘ ϕleft F.∘ [ ≡.cong₂ _·_ x≡εx ≡.refl ] F.∘ [ ε≡xx⁻¹ ]) p₀
        ≡⟨ ϕleft-homo ε x (x ⁻¹) _ ⟩
          (ϕleft F.∘ [ assoc ε x (x ⁻¹) ] F.∘ [ ≡.cong₂ _·_ x≡εx ≡.refl ] F.∘ [ ε≡xx⁻¹ ]) p₀
        ≡⟨ ϕleft-id-with (inverseʳ x) _ ⟩
          ([ ≡.cong (ε ·_) (inverseʳ x) ⨾ identityʳ ε ]
             F.∘ [ assoc ε x (x ⁻¹) ]
             F.∘ [ ≡.cong₂ _·_ x≡εx ≡.refl ]
             F.∘ [ ε≡xx⁻¹ ]) p₀
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
          (ϕleft F.∘ [ ε≡xx⁻¹ {x} ] F.∘ ϕleft F.∘ [ x≡εx ]) p
        ≡⟨ ≡.cong ϕleft (ϕleft-≡-natural (ε≡xx⁻¹ {x}) ≡.refl _) ⟩
          (ϕleft F.∘ ϕleft F.∘ [ ≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl ] F.∘ [ x≡εx ]) p
        ≡⟨ ϕleft-homo x (x ⁻¹) x _ ⟩
          (ϕleft F.∘ [ assoc x (x ⁻¹) x ] F.∘ [ ≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl ] F.∘ [ x≡εx ]) p
        ≡⟨ ϕleft-id-with (inverseˡ x) _ ⟩
          ([ ≡.cong (x ·_) (inverseˡ x) ⨾ identityʳ x ]
             F.∘ [ assoc x (x ⁻¹) x ]
             F.∘ [ ≡.cong₂ _·_ (ε≡xx⁻¹ {x}) ≡.refl ]
             F.∘ [ x≡εx ]) p
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
  
  std-right : (x y : S) → P ε → P ε
  std-right x y = actionStd .Action.ϕright {x} {y}

  std-right-is-id : (x y : S) → std-right x y ≗ F.id
  std-right-is-id x y p = begin
      std-right x y p
    ≡⟨⟩
      ϕleft
        ([ ≡.sym (identityˡ y) ]
         (ϕright (ϕleft ([ ≡.sym (inverseʳ (x · y)) ] p))))
    ≡⟨ _ ⟩
      p
    ∎
    where open ≡.≡-Reasoning