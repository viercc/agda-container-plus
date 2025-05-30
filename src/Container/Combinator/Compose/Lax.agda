{-# OPTIONS --without-K --safe #-}

-- Properties of container compositions regarding lax structures
module Container.Combinator.Compose.Lax where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Data.Container.Core

open import Container.Morphism.Equality using (_≈_; mk≈)

import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Container.Combinator.Compose
open import Container.Lax
open import Container.Effect.Functor.Lax

module _ {c c' d d'} (C : Container c c') (D : Container d d') where
  open Container C
    renaming (Shape to C₀; Position to C₁)
  open Container D
    renaming (Shape to D₀; Position to D₁)

  private
    CD₀ : Set _
    CD₀ = ⟦ C₀ ▷ C₁ ⟧ D₀

    CD₁ : CD₀ → Set _
    CD₁ = ◇ (C₀ ▷ C₁) D₁
  
  private
    module laxity where
      open LaxEquality (strict C) (≡.setoid D₀) using ()
        renaming (
          LaxEq to _∼_;
          isEquivalence to ∼-isEquivalence;
          setoid to CD₀-setoid
        )
        public

      open IsEquivalence ∼-isEquivalence

      subst : {cd cd′ : CD₀} → cd ∼ cd′ → CD₁ cd → CD₁ cd′
      subst {cd = c , v} {cd′ = c′ , v′}
        (mkLaxEq ≡.refl eqV) (mk◇ (pc , pd))
          = mk◇ (pc , ≡.subst D₁ (eqV pc) pd)
      
      subst-refl : {cd : CD₀} → {p : CD₁ cd} → p ≡ subst refl p
      subst-refl {cd = c , v } {p = mk◇ (pc , pd)} = ≡.refl
      
      subst-subst : ∀ {cd cd′ cd″}
        (eq₁ : cd ∼ cd′) {eq₂ : cd′ ∼ cd″}
        {p : CD₁ cd}
        → subst eq₂ (subst eq₁ p) ≡ subst (trans eq₁ eq₂) p
      subst-subst {cd = c , v} {cd′ = c′ , v′} {cd″ = c″ , v″}
        (mkLaxEq ≡.refl eq₁V) {eq₂ = mkLaxEq ≡.refl eq₂V}
        {p = mk◇ (pc , pd)} = ◇-util.◇-dcong D₁ ≡.refl proof
          where
            open ≡.≡-Reasoning
            proof : ≡.subst D₁ (eq₂V pc) (≡.subst D₁ (eq₁V pc) pd)
              ≡ ≡.subst D₁
                  (≡.trans (eq₁V pc) (≡.trans (eq₂V pc) ≡.refl))
                      pd
            proof = begin
                ≡.subst D₁ (eq₂V pc) (≡.subst D₁ (eq₁V pc) pd)
              ≡⟨⟩
                ≡.subst D₁ ≡.refl (≡.subst D₁ (eq₂V pc) (≡.subst D₁ (eq₁V pc) pd))
              ≡⟨ ≡.subst-subst (eq₂V pc) ⟩
                ≡.subst D₁ (≡.trans (eq₂V pc) ≡.refl) (≡.subst D₁ (eq₁V pc) pd)
              ≡⟨ ≡.subst-subst (eq₁V pc) ⟩
                ≡.subst D₁ (≡.trans (eq₁V pc) (≡.trans (eq₂V pc) ≡.refl)) pd
              ∎
      
      subst-sym-subst : ∀ {cd cd′}
        (eq : cd ∼ cd′) {p : CD₁ cd}
        → subst (sym eq) (subst eq p) ≡ p
      subst-sym-subst {cd = c , v} {cd′ = c′ , v′}
        eq@(mkLaxEq ≡.refl eqV) 
        {p = mk◇ (pc , pd)} = ◇-util.◇-dcong D₁ ≡.refl proof
          where
            open ≡.≡-Reasoning
            proof :
              ≡.subst D₁ (≡.trans (≡.sym (eqV pc)) ≡.refl)
                (≡.subst D₁ (eqV pc) pd)
              ≡ pd
            proof =
              ≡.trans (≡.cong (λ e → ≡.subst D₁ e (≡.subst D₁ (eqV pc) pd)) (≡.trans-reflʳ (≡.sym (eqV pc))))
                (≡.subst-sym-subst (eqV pc))
      
      subst-subst-sym : ∀ {cd cd′}
        (eq : cd ∼ cd′) {p : CD₁ cd′}
        → subst eq (subst (sym eq) p) ≡ p
      subst-subst-sym {cd = c , v} {cd′ = c′ , v′}
        eq@(mkLaxEq ≡.refl eqV)
        {p = mk◇ (pc , pd)} = ◇-util.◇-dcong D₁ ≡.refl proof
          where
            open ≡.≡-Reasoning
            proof :
              ≡.subst D₁ (eqV pc)
                (≡.subst D₁ (≡.trans (≡.sym (eqV pc)) ≡.refl) pd)
              ≡ pd
            proof =
              ≡.trans (≡.cong (λ e → ≡.subst D₁ (eqV pc) (≡.subst D₁ e pd)) (≡.trans-reflʳ _))
                (≡.subst-subst-sym (eqV pc))

  laxity-Comp : Laxity (Comp C D)
  laxity-Comp = record { laxity }