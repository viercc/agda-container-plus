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

open import Container.Morphism.Equality as ≈
  using (_≈_; mk≈)

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
        (mkLaxEq eqS eqV) (mk◇ (pc , pd))
          = mk◇ (≡.subst C₁ eqS pc , ≡.subst D₁ (eqV pc) pd)
      
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

  laxComp : LaxContainer _ _
  laxComp = record { laxity = laxity-Comp }



module _ {c c' d d'} {C : Container c c'} {D : Container d d'} where
  open Container C renaming (Shape to C₀; Position to C₁)
  open Container D renaming (Shape to D₀; Position to D₁)
  
  -- map₁, map₂ are WellDefined
  map₁-well : ∀
    (ff : C ⇒ D) {e e'} (E : Container e e')
    → WellDefined (laxComp C E) (laxComp D E) (map₁ ff)
  map₁-well ff@(f ▷ f#) E = record {
      shape-cong = shape-cong;
      position-cong = pos-cong
    }
    where
      open Container E renaming (Shape to E₀; Position to E₁)
      module LaxCE = LaxContainer (laxComp C E)
      open LaxCE using () renaming (_∼_ to _∼₁_)
      module LaxDE = LaxContainer (laxComp D E)
      open LaxDE using () renaming (_∼_ to _∼₂_)

      shape-cong : {cx cy : ⟦ C ⟧ E₀} → cx ∼₁ cy → ⟪ ff ⟫ cx ∼₂ ⟪ ff ⟫ cy
      shape-cong {cy = _ , v₂} (mkLaxEq shapeEq posEq) =
        mkLaxEq (≡.cong f shapeEq)
          (λ p → ≡.trans
            (posEq (f# p))
            (≡.cong v₂ (≡.subst-application D₁ (F.λ- f#) shapeEq))
          )
      
      pos-cong : {cx cy : ⟦ C ⟧ E₀} → {pq : ◇ D E₁ (⟪ ff ⟫ cx)}
        → (eq : cx ∼₁ cy) → LaxCE.subst eq (C◇.map₁ ff pq) ≡ C◇.map₁ ff (LaxDE.subst (shape-cong eq) pq)
      pos-cong {pq = mk◇ (p , q)}
        (mkLaxEq ≡.refl v₁≗v₂) = ◇-util.◇-dcong E₁
          ≡.refl
          (≡.cong (λ e → ≡.subst E₁ e q) (≡.sym (≡.trans-reflʳ _)))
  
  map₂-well : ∀
    {e e'} (E : Container e e') (ff : C ⇒ D)
    → WellDefined (laxComp E C) (laxComp E D) (map₂ ff)
  map₂-well E ff@(f ▷ f#) = record {
      shape-cong = shape-cong;
      position-cong = pos-cong
    }
    where
      open Container E renaming (Shape to E₀; Position to E₁)
      module LaxEC = LaxContainer (laxComp E C)
      open LaxEC using () renaming (_∼_ to _∼₁_)
      module LaxED = LaxContainer (laxComp E D)
      open LaxED using () renaming (_∼_ to _∼₂_)

      shape-cong : {ex ey : ⟦ E ⟧ C₀} → ex ∼₁ ey → map f ex ∼₂ map f ey
      shape-cong {ey = _ , v₂} (mkLaxEq shapeEq posEq) =
        mkLaxEq shapeEq λ p → ≡.cong f (posEq p)
      
      pos-cong : {ex ey : ⟦ E ⟧ C₀} → {pq : ◇ E D₁ (map f ex)}
        → (eq : ex ∼₁ ey)
        → LaxEC.subst eq (C◇.map₂ f# (◇-util.◇-dinat D₁ f pq))
            ≡
          C◇.map₂ f# (◇-util.◇-dinat D₁ f (LaxED.subst (shape-cong eq) pq))
      pos-cong {pq = mk◇ (p , q)}
        (mkLaxEq ≡.refl v₁≗v₂) = ◇-util.◇-dcong C₁ ≡.refl
          (≡.subst-application D₁ (F.λ- f#) (v₁≗v₂ p))

  -- Congruences of map₁, map₂ for Comp holds
  -- only up to laxComp
  map₁-cong : ∀
      {ff gg : C ⇒ D} (ff≈gg : ff ≈ gg)
      {e e'} (E : Container e e')
    → Lax≈ (laxComp D E) (map₁ ff) (map₁ gg)
  map₁-cong {ff = ff@(f ▷ f#)} {gg = gg@(g ▷ g#)}
    (mk≈ eqS eqP) E = mkLax≈ shapeEq posEq
    where
      open Container E renaming (Shape to E₀; Position to E₁)
      module LaxDE = LaxContainer (laxComp D E)
      open LaxDE using (_∼_)

      shapeEq : ∀ (cx : ⟦ C ⟧ E₀) → ⟪ ff ⟫ cx ∼ ⟪ gg ⟫ cx
      shapeEq (c₀ , v) = mkLaxEq (eqS c₀) (λ p → ≡.cong v (eqP c₀ p))

      posEq : ∀ (cx : ⟦ C ⟧ E₀) (pq : ◇ D E₁ (⟪ ff ⟫ cx)) →
        C◇.map₁ ff pq ≡ C◇.map₁ gg (LaxDE.subst (shapeEq cx) pq)
      posEq (c₀ , v) (mk◇ (p , q)) = ◇-util.◇-dcong E₁ eq-p eq-q
        where
          eq-p : f# p ≡ g# (≡.subst D₁ (eqS c₀) p)
          eq-p = eqP c₀ p

          eq-q : ≡.subst (E₁ F.∘ v) eq-p q ≡ ≡.subst E₁ (≡.cong v eq-p) q
          eq-q = ≡.subst-∘ eq-p
  
  map₂-cong : ∀
      {e e'} (E : Container e e')
      {ff gg : C ⇒ D} (ff≈gg : ff ≈ gg)
    → Lax≈ (laxComp E D) (map₂ ff) (map₂ gg)
  map₂-cong E
    {ff = ff@(f ▷ f#)} {gg = gg@(g ▷ g#)} (mk≈ eqS eqP)
      = mkLax≈ shapeEq posEq
    where
      open Container E renaming (Shape to E₀; Position to E₁)
      module LaxED = LaxContainer (laxComp E D)
      open LaxED using (_∼_)
      
      shapeEq : ∀ (ex : ⟦ E ⟧ C₀) → map f ex ∼ map g ex
      shapeEq (e₀ , v) = mkLaxEq ≡.refl (λ p → eqS (v p))

      posEq : ∀ (ex : ⟦ E ⟧ C₀) (pq : ◇ E D₁ (map f ex)) →
        C◇.map₂ f# (◇-util.◇-dinat D₁ f pq)
          ≡
        C◇.map₂ g#
          (◇-util.◇-dinat D₁ g (LaxED.subst (shapeEq ex) pq))
      posEq (_ , v) (mk◇ (p , q)) = ◇-util.◇-dcong C₁ ≡.refl eq-q
        where
          eq-q : _
          eq-q = eqP (v p) q