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

module lemmata {s p} (C* : LaxContainer s p) where
  open LaxContainer C*

  subst-reflexive : ∀ {x y} {p : P x}
    → (eq : x ≡ y) → ≡.subst P eq p ≡ subst (reflexive eq) p
  subst-reflexive ≡.refl = subst-refl

  -- Needs IsGroupoid (if it had existed) instead of IsEquivalence
  postulate
    trans-assoc : ∀ {x y z w} (p : x ∼ y) {q : y ∼ z} {r : z ∼ w}
      → trans (trans p q) r ≡ trans p (trans q r)
    
    trans-reflˡ : ∀ {x y} (eq : x ∼ y)
      → trans refl eq ≡ eq
    
    trans-reflʳ : ∀ {x y} (eq : x ∼ y)
      → trans eq refl ≡ eq
    
    trans-symˡ : ∀ {x y} (eq : x ∼ y)
      → trans (sym eq) eq ≡ refl
    
    trans-symʳ : ∀ {x y} (eq : x ∼ y)
      → trans eq (sym eq) ≡ refl
  
  sym-refl : ∀ {x} → sym refl ≡ refl {x = x}
  sym-refl =
    begin
      sym refl
    ≡⟨ trans-reflˡ (sym refl) ⟨
      trans refl (sym refl)
    ≡⟨ trans-symʳ refl ⟩
      refl
    ∎
    where open ≡.≡-Reasoning

  subst-sym-reflexive : ∀ {x y} {p : P y}
    → (eq : x ≡ y) → subst (sym (reflexive eq)) p ≡ ≡.subst P (≡.sym eq) p
  subst-sym-reflexive {p = p} ≡.refl =
    begin
      subst (sym refl) p
    ≡⟨ ≡.cong (λ e → subst e p) sym-refl ⟩
      subst refl p
    ≡⟨ subst-refl ⟨
      p
    ∎
    where open ≡.≡-Reasoning
  

  -- subst-sym-subst and subst-subst-sym are theorems now,
  -- but it is not guaranteed that it is the unique impl.
  subst-sym-subst-default : ∀ {x y} (eq : x ∼ y) {p : P x}
    → subst (sym eq) (subst eq p) ≡ p
  subst-sym-subst-default eq {p = p} =
    ≡.trans (subst-subst eq)
      (≡.trans (≡.cong (λ e → subst e p) (trans-symʳ eq))
        (≡.sym subst-refl))
  
  subst-subst-sym-default : ∀ {x y} (eq : x ∼ y) {p : P y}
    → subst eq (subst (sym eq) p) ≡ p
  subst-subst-sym-default eq {p = p} =
    ≡.trans (subst-subst (sym eq))
      (≡.trans (≡.cong (λ e → subst e p) (trans-symˡ eq))
        (≡.sym subst-refl))
  
  postulate
    isDefault-subst-sym-subst : ∀ {x y} →
      subst-sym-subst {x} {y} ≡ subst-sym-subst-default {x} {y}
    isDefault-subst-subst-sym : ∀ {x y} →
      subst-subst-sym {x} {y} ≡ subst-subst-sym-default {x} {y}
  
  -- Given the above impl:
  subst-sym-subst-subst : ∀ {x y} (eq : x ∼ y) {p : P x}
    → ≡.trans (≡.sym (subst-subst-sym eq {p = subst eq p}))
        (≡.cong (subst eq) (subst-sym-subst eq))
        ≡
      ≡.refl
  subst-sym-subst-subst eq = _

module _ {c c' d d'} (C* : LaxContainer c c') (D* : LaxContainer d d') where
  module C = LaxContainer C*
  module D = LaxContainer D*
  open C using ()
    renaming (S to C₀; P to C₁; _∼_ to _∼c∼_)
  open D using ()
    renaming (S to D₀; P to D₁; _∼_ to _∼d∼_)

  private
    CD₀ : Set _
    CD₀ = ⟦ C₀ ▷ C₁ ⟧ D₀

    CD₁ : CD₀ → Set _
    CD₁ = ◇ (C₀ ▷ C₁) D₁
  
  private
    module laxity where
      open LaxEquality C* D.S-setoid using ()
        renaming (
          LaxEq to _∼_;
          isEquivalence to ∼-isEquivalence;
          setoid to CD₀-setoid
        )
        public

      open IsEquivalence ∼-isEquivalence

      subst : {cd cd′ : CD₀} → cd ∼ cd′ → CD₁ cd → CD₁ cd′
      subst {cd = c , v} {cd′ = c′ , v′}
        (mkLaxEq eqC eqV) (mk◇ (pc , pd))
          = mk◇ (C.subst eqC pc , D.subst (eqV pc) pd)
      
      subst-refl : {cd : CD₀} → {p : CD₁ cd} → p ≡ subst refl p
      subst-refl {cd = c , v } {p = mk◇ (pc , pd)} =
        ◇-util.◇-dcong D₁ C.subst-refl proof
        where
          proof :
            ≡.subst (D₁ F.∘′ v) C.subst-refl pd
              ≡
            D.subst (D.reflexive (≡.cong v C.subst-refl)) pd
          proof =
            begin
              ≡.subst (D₁ F.∘′ v) C.subst-refl pd
            ≡⟨ ≡.subst-∘ {P = D₁} C.subst-refl ⟩
              ≡.subst D₁ (≡.cong v C.subst-refl) pd
            ≡⟨ props.subst-reflexive D* _ ⟩
              D.subst (D.reflexive (≡.cong v C.subst-refl)) pd
            ∎
            where open ≡.≡-Reasoning
      
      subst-subst : ∀ {cd cd′ cd″}
        (eq₁ : cd ∼ cd′) {eq₂ : cd′ ∼ cd″}
        {p : CD₁ cd}
        → subst eq₂ (subst eq₁ p) ≡ subst (trans eq₁ eq₂) p
      subst-subst {cd = c , v} {cd′ = c′ , v′} {cd″ = c″ , v″}
        eq₁@(mkLaxEq eq₁C eq₁V) {eq₂ = eq₂@(mkLaxEq eq₂C eq₂V)}
        {p = mk◇ (pc , pd)} = ◇-util.◇-dcong D₁ eqPC eqPD
        where
          open LaxEquality.LaxEq (trans eq₁ eq₂)
            renaming (shapeEq to eqC; positionEq to eqV)

          eqPC :
            C.subst eq₂C (C.subst eq₁C pc) ≡ C.subst eqC pc
          eqPC = C.subst-subst eq₁C

          step₁ : v pc ∼d∼ v′ (C.subst eq₁C pc)
          step₁ = eq₁V pc

          step₂ : v′ (C.subst eq₁C pc) ∼d∼ v″ (C.subst eq₂C (C.subst eq₁C pc))
          step₂ = eq₂V _

          step₃ : v″ (C.subst eq₂C (C.subst eq₁C pc)) ∼d∼ v″ (C.subst eqC pc)
          step₃ = D.reflexive (≡.cong v″ (C.subst-subst eq₁C))

          eqPD :
            ≡.subst (D₁ F.∘′ v″) (C.subst-subst eq₁C)
              (D.subst step₂ (D.subst step₁ pd))
             ≡ D.subst (eqV pc) pd
          eqPD =
            begin
              ≡.subst (D₁ F.∘′ v″) (C.subst-subst eq₁C)
                (D.subst step₂ (D.subst step₁ pd))
            ≡⟨ ≡.subst-∘ (C.subst-subst eq₁C) ⟩
              ≡.subst D₁ (≡.cong v″ (C.subst-subst eq₁C))
                (D.subst step₂ (D.subst step₁ pd))
            ≡⟨ props.subst-reflexive D* _ ⟩
              D.subst step₃ (D.subst step₂ (D.subst step₁ pd))
            -- Proofs written using ≈-syntax have extraneous `refl` at
            -- the end (to guide type inference)
            ≡⟨ D.subst-refl ⟩
              D.subst D.refl (D.subst step₃ (D.subst step₂ (D.subst step₁ pd)))
            ≡⟨ D.subst-subst step₃ ⟩
              D.subst (D.trans step₃ D.refl) (D.subst step₂ (D.subst step₁ pd))
            ≡⟨ D.subst-subst step₂ ⟩
              D.subst (D.trans step₂ (D.trans step₃ D.refl)) (D.subst step₁ pd)
            ≡⟨ D.subst-subst step₁ ⟩
              D.subst (D.trans step₁ (D.trans step₂ (D.trans step₃ D.refl))) pd
            ≡⟨⟩
              D.subst (eqV pc) pd
            ∎
            where
              open ≡.≡-Reasoning
      
      subst-sym-subst : ∀ {cd cd′}
        (eq : cd ∼ cd′) {p : CD₁ cd}
        → subst (sym eq) (subst eq p) ≡ p
      subst-sym-subst {cd = c , v} {cd′ = c′ , v′}
        eq@(mkLaxEq eqC eqV) 
        {p = mk◇ (pc , pd)} = ◇-util.◇-dcong D₁ eqPC eqPD
        where
          open LaxEquality.LaxEq (sym eq)
            renaming (shapeEq to eqC⁻; positionEq to eqV⁻)

          eqPC : C.subst eqC⁻ (C.subst eqC pc) ≡ pc
          eqPC = C.subst-sym-subst eqC

          eq-cc⁻c-r : C.subst eqC (C.subst eqC⁻ (C.subst eqC pc)) ≡ C.subst eqC pc
          eq-cc⁻c-r = ≡.cong (C.subst eqC) eqPC

          eq-cc⁻c-l : C.subst eqC (C.subst eqC⁻ (C.subst eqC pc)) ≡ C.subst eqC pc
          eq-cc⁻c-l = C.subst-subst-sym eqC

          step₁ : v pc ∼d∼ v′ (C.subst eqC pc)
          step₁ = eqV pc

          step₂ : v′ (C.subst eqC pc) ∼d∼ v′ (C.subst eqC (C.subst eqC⁻ (C.subst eqC pc)))
          step₂ = D.sym (D.reflexive (≡.cong v′ eq-cc⁻c-l))

          step₃-gen : ∀ pc → v′ (C.subst eqC pc) ∼d∼ v pc
          step₃-gen pc = D.sym (eqV pc)

          step₃ : _
          step₃ = step₃-gen (C.subst eqC⁻ (C.subst eqC pc))

          step₄-gen : ∀ v → v (C.subst eqC⁻ (C.subst eqC pc)) ∼d∼ v pc
          step₄-gen v = D.reflexive (≡.cong v eqPC)

          step₄ : v (C.subst eqC⁻ (C.subst eqC pc)) ∼d∼ v pc
          step₄ = step₄-gen v

          step₄′ : _
          step₄′ = step₄-gen (v′ F.∘′ C.subst eqC)
          
          step₂-step₄-cancel : ∀ pd → D.subst step₄′ (D.subst step₂ pd) ≡ pd
          step₂-step₄-cancel pd =
              begin
                D.subst step₄′ (D.subst step₂ pd)
              ≡⟨ props.subst-reflexive D* _ ⟨
                ≡.subst D₁ (≡.cong (v′ F.∘′ C.subst eqC) eqPC) (D.subst step₂ pd)
              ≡⟨ ≡.cong (≡.subst D₁ _) (lemmata.subst-sym-reflexive D* _) ⟩
                ≡.subst D₁ (≡.cong (v′ F.∘′ C.subst eqC) eqPC)
                  (≡.subst D₁ (≡.sym (≡.cong v′ eq-cc⁻c-l)) pd)
              ≡⟨ ≡.subst-subst (≡.sym (≡.cong v′ eq-cc⁻c-l)) ⟩
                ≡.subst D₁ (≡.trans
                  (≡.sym (≡.cong v′ eq-cc⁻c-l))
                  (≡.cong (v′ F.∘′ C.subst eqC) eqPC)
                ) pd
              ≡⟨ ≡.cong (λ e → ≡.subst D₁ e pd) (
                let open ≡.≡-Reasoning in
                begin
                  ≡.trans
                    (≡.sym (≡.cong v′ eq-cc⁻c-l))
                    (≡.cong (v′ F.∘′ C.subst eqC) eqPC)
                ≡⟨ ≡.cong₂ ≡.trans (≡.sym-cong _) (≡.cong-∘ eqPC) ⟩
                  ≡.trans
                    (≡.cong v′ (≡.sym eq-cc⁻c-l))
                    (≡.cong v′ eq-cc⁻c-r)
                ≡⟨ ≡.trans-cong (≡.sym eq-cc⁻c-l) ⟩
                  ≡.cong v′
                    (≡.trans (≡.sym eq-cc⁻c-l) eq-cc⁻c-r)
                ≡⟨ ≡.cong (≡.cong v′) (lemmata.subst-sym-subst-subst C* eqC) ⟩
                  ≡.refl
                ∎
              )⟩
                pd
              ∎
              where open ≡.≡-Reasoning

          aux : ∀ (pd : D₁ (v′ (C.subst eqC pc)))
            → D.subst (eqV⁻ (C.subst eqC pc)) pd
                ≡ D.subst step₃ (D.subst step₂ pd)
          aux pd =
            begin
              D.subst (eqV⁻ (C.subst eqC pc)) pd
            ≡⟨⟩
              D.subst (D.trans step₂ (D.trans step₃ D.refl)) pd
            ≡⟨ D.subst-subst step₂ ⟨
              D.subst (D.trans step₃ D.refl) (D.subst step₂ pd)
            ≡⟨ D.subst-subst step₃ ⟨
              D.subst D.refl (D.subst step₃ (D.subst step₂ pd))
            ≡⟨ D.subst-refl ⟨
              D.subst step₃ (D.subst step₂ pd)
            ∎
            where open ≡.≡-Reasoning

          eqPD :
            ≡.subst (λ p → D₁ (v p)) eqPC
              (D.subst (eqV⁻ (C.subst eqC pc))
                (D.subst (eqV pc) pd))
            ≡ pd
          eqPD = 
            begin
              ≡.subst (λ p → D₁ (v p)) eqPC
                (D.subst (eqV⁻ (C.subst eqC pc))
                  (D.subst (eqV pc) pd))
            ≡⟨ ≡.subst-∘ eqPC ⟩
              ≡.subst D₁ (≡.cong v eqPC)
                (D.subst (eqV⁻ (C.subst eqC pc))
                  (D.subst step₁ pd))
            ≡⟨ props.subst-reflexive D* _ ⟩
              D.subst step₄
                (D.subst (eqV⁻ (C.subst eqC pc))
                  (D.subst step₁ pd))
            ≡⟨ ≡.cong (D.subst step₄) (aux _) ⟩
              D.subst step₄
                (D.subst step₃
                  (D.subst step₂
                    (D.subst step₁ pd)))
            ≡⟨ props.subst-trans-reflexive-comm D* step₃-gen eqPC _ ⟩
              D.subst (step₃-gen pc)
                (D.subst step₄′
                  (D.subst step₂
                    (D.subst step₁ pd)))
            ≡⟨ ≡.cong (D.subst (step₃-gen pc)) (step₂-step₄-cancel _) ⟩
              D.subst (step₃-gen pc)
                (D.subst step₁ pd)
            ≡⟨ D.subst-sym-subst step₁ ⟩
              pd
            ∎
            where open ≡.≡-Reasoning
      
      subst-subst-sym : ∀ {cd cd′}
        (eq : cd ∼ cd′) {p : CD₁ cd′}
        → subst eq (subst (sym eq) p) ≡ p
      subst-subst-sym {cd = c , v} {cd′ = c′ , v′}
        eq@(mkLaxEq eqC eqV) 
        {p = mk◇ (pc , pd)} = ◇-util.◇-dcong D₁ eqPC eqPD
        where
          open LaxEquality.LaxEq (sym eq)
            renaming (shapeEq to eqC⁻; positionEq to eqV⁻)

          eqPC : C.subst eqC (C.subst eqC⁻ pc) ≡ pc
          eqPC = C.subst-subst-sym eqC

          step₁ : _
          step₁ = D.sym (D.reflexive (≡.cong v′ eqPC))

          step₂ : _
          step₂ = D.sym (eqV (C.subst eqC⁻ pc))

          step₃ : v (C.subst eqC⁻ pc) ∼d∼ v′ (C.subst eqC (C.subst eqC⁻ pc))
          step₃ = eqV (C.subst eqC⁻ pc)

          step₄ : v′ (C.subst eqC (C.subst eqC⁻ pc)) ∼d∼ v′ pc
          step₄ = D.reflexive (≡.cong v′ eqPC)

          aux : D.subst (eqV⁻ pc) pd ≡ D.subst step₂ (D.subst step₁ pd)
          aux =
            begin
              D.subst (eqV⁻ pc) pd
            ≡⟨⟩
              D.subst (D.trans step₁ (D.trans step₂ D.refl)) pd
            ≡⟨ D.subst-subst step₁ ⟨
              D.subst _ (D.subst step₁ pd)
            ≡⟨ D.subst-subst step₂ ⟨
              D.subst D.refl (D.subst step₂ (D.subst step₁ pd))
            ≡⟨ D.subst-refl ⟨
              D.subst step₂ (D.subst step₁ pd)
            ∎
            where open ≡.≡-Reasoning

          eqPD : ≡.subst (D₁ F.∘′ v′) eqPC
            (D.subst (eqV (C.subst eqC⁻ pc))
              (D.subst (eqV⁻ pc) pd))
            ≡ pd
          eqPD =
            begin
              ≡.subst (D₁ F.∘′ v′) eqPC
                (D.subst step₃
                  (D.subst (eqV⁻ pc) pd))
            ≡⟨ ≡.subst-∘ eqPC ⟩
              ≡.subst D₁ (≡.cong v′ eqPC)
                (D.subst step₃
                  (D.subst (eqV⁻ pc) pd))
            ≡⟨ props.subst-reflexive D* _ ⟩
              D.subst step₄
                (D.subst step₃
                  (D.subst (eqV⁻ pc) pd))
            ≡⟨ ≡.cong (D.subst step₄ F.∘′ D.subst step₃) aux ⟩
              D.subst step₄ (D.subst step₃
                (D.subst step₂ (D.subst step₁ pd)))
            ≡⟨ ≡.cong (D.subst step₄) (D.subst-subst-sym step₃) ⟩
              D.subst step₄ (D.subst step₁ pd)
            ≡⟨ D.subst-subst-sym step₄ ⟩
              pd
            ∎
            where open ≡.≡-Reasoning

  laxity-Comp : Laxity (Comp ⌊ C* ⌋ ⌊ D* ⌋)
  laxity-Comp = record { laxity }