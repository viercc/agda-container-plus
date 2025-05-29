{-# OPTIONS --without-K --safe #-}

open import Level

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

import Function as F

open import Data.Container.Core
import Data.Container.Morphism as CM
open CM using (_∘_)
open import Container.Morphism.Equality

module Container.Lax where

-- Container with lax equality on Shape
record Laxity {s p : Level} (C : Container s p) : Set (suc (s ⊔ p)) where
  open Container C renaming (Shape to S; Position to P)
  infix 4 _∼_
  field
    _∼_ : Rel S s
    instance
      ∼-isEquivalence : IsEquivalence _∼_
  
  open IsEquivalence ∼-isEquivalence public

  field
    subst : ∀ {x y} → x ∼ y → P x → P y
    subst-refl : ∀ {x} {p : P x} → p ≡ subst refl p
    subst-subst : ∀ {x y z} (eq₁ : x ∼ y) {eq₂ : y ∼ z} {p : P x}
      → subst eq₂ (subst eq₁ p) ≡ subst (trans eq₁ eq₂) p
    subst-sym-subst : ∀ {x y} (eq : x ∼ y) {p : P x}
      → subst (sym eq) (subst eq p) ≡ p
    subst-subst-sym : ∀ {x y} (eq : x ∼ y) {p : P y}
      → subst eq (subst (sym eq) p) ≡ p

  S-setoid : Setoid s s
  S-setoid = record { isEquivalence = ∼-isEquivalence }

record LaxContainer (s p : Level) : Set (suc (s ⊔ p)) where
  constructor mkLaxContainer
  field
    Carrier : Container s p
    laxity : Laxity Carrier
  
  open Container Carrier
    renaming (Shape to S; Position to P)
    public
  open Laxity laxity public

module props {s p} (C* : LaxContainer s p) where
  open LaxContainer C*

  subst-reflexive : ∀ {x y} {p : P x}
    → (eq : x ≡ y) → ≡.subst P eq p ≡ subst (reflexive eq) p
  subst-reflexive ≡.refl = subst-refl

-- View a Container as LaxContainer equipped with
-- strict (propositional) equality: _≡_

strictLaxity : ∀ {s p} → (C : Container s p) → Laxity C
strictLaxity (S ▷ P) = record {
    ∼-isEquivalence = ≡.isEquivalence;
    subst = ≡.subst P;
    subst-refl = ≡.refl;
    subst-subst = ≡.subst-subst;
    subst-sym-subst = ≡.subst-sym-subst;
    subst-subst-sym = ≡.subst-subst-sym
  }

strict : ∀ {s p} → Container s p → LaxContainer s p
strict C@(S ▷ P) = record {
    Carrier = C;
    laxity = strictLaxity C
  }

-- Strip laxity off from LaxContainer
⌊_⌋ : {s p : Level} → LaxContainer s p → Container s p
⌊_⌋ = LaxContainer.Carrier

-- Morphism is well-defined in terms of lax
record WellDefined
  {c c' d d'}
  (C* : LaxContainer c c')
  (D* : LaxContainer d d')
  (ff : ⌊ C* ⌋ ⇒ ⌊ D* ⌋)
    : Set (c ⊔ c' ⊔ d ⊔ d') where
  open _⇒_ ff renaming (shape to f; position to f#)
  open LaxContainer C*
    using ()
    renaming (S to C₀; _∼_ to _∼₁_; subst to subst₁)
  open LaxContainer D*
    using ()
    renaming (P to D₁; _∼_ to _∼₂_; subst to subst₂)

  field
    shape-cong : ∀ {x y : C₀} → x ∼₁ y → f x ∼₂ f y
    position-cong : ∀ {x y : C₀} {pd : D₁ (f x)}
      → (eq : x ∼₁ y) → subst₁ eq (f# pd) ≡ f# (subst₂ (shape-cong eq) pd)

-- Every morphism which has strict domain is always WellDefined
strictWellDefined :
  {c c' d d' : Level}
  {C : Container c c'}
  (D* : LaxContainer d d')
  (ff : C ⇒ ⌊ D* ⌋)
  → WellDefined (strict C) D* ff
strictWellDefined {C = C} D* (f ▷ f#) = record {
    shape-cong = shape-cong;
    position-cong = position-cong 
  }
  where
    open Container C renaming (Shape to C₀; Position to C₁)
    open LaxContainer D*
      using (refl; subst-refl)
      renaming (S to D₀; P to D₁; _∼_ to _∼₂_; subst to substD)
    
    shape-cong : {x y : C₀} → x ≡ y → f x ∼₂ f y
    shape-cong ≡.refl = refl

    position-cong : {x y : C₀} {pd : D₁ (f x)}
      → (eq : x ≡ y) → ≡.subst C₁ eq (f# pd) ≡ f# (substD (shape-cong eq) pd)
    position-cong ≡.refl = ≡.cong f# subst-refl

-- identity is well-defined
id-well : 
  {c c' : Level} (C* : LaxContainer c c')
  → WellDefined C* C* (CM.id ⌊ C* ⌋)
id-well _ = record {
    shape-cong = F.id;
    position-cong = λ _ → ≡.refl
  }

-- composition of well-defined morphism is well-defined again
∘-well :
  {c c' d d' e e' : Level}
  {C* : LaxContainer c c'} {D* : LaxContainer d d'} {E* : LaxContainer e e'}
  {ff : ⌊ D* ⌋ ⇒ ⌊ E* ⌋} {gg : ⌊ C* ⌋ ⇒ ⌊ D* ⌋}
  → WellDefined D* E* ff
  → WellDefined C* D* gg
  → WellDefined C* E* (ff ∘ gg)
∘-well
  {C* = C*} {D* = D*} {E* = E*}
  {ff = f ▷ f#} {gg = g ▷ g#}
  well-ff well-gg = record {
      shape-cong = shape-cong;
      position-cong = position-cong 
    }
  where
    open LaxContainer C* using ()
      renaming (S to C₀; _∼_ to _∼₁_; subst to subst₁)
    open LaxContainer D* using ()
      renaming (         _∼_ to _∼₂_; subst to subst₂)
    open LaxContainer E* using ()
      renaming (P to E₁; _∼_ to _∼₃_; subst to subst₃)
    module Wff = WellDefined well-ff
    module Wgg = WellDefined well-gg
    
    shape-cong : {x y : C₀} → x ∼₁ y → f (g x) ∼₃ f (g y)
    shape-cong x∼y = Wff.shape-cong (Wgg.shape-cong x∼y)

    position-cong : {x y : C₀} {pe : E₁ (f (g x))}
      → (eq : x ∼₁ y)
      → subst₁ eq (g# (f# pe)) ≡ g# (f# (subst₃ (shape-cong eq) pe))
    position-cong {pe = pe} eq =
      begin
        subst₁ eq (g# (f# pe))
      ≡⟨ Wgg.position-cong eq ⟩
        g# (subst₂ (Wgg.shape-cong eq) (f# pe))
      ≡⟨ ≡.cong g# (Wff.position-cong (Wgg.shape-cong eq)) ⟩
        g# (f# (subst₃ (Wff.shape-cong (Wgg.shape-cong eq)) pe))
      ≡⟨⟩
        g# (f# (subst₃ (shape-cong eq) pe))
      ∎
      where open ≡.≡-Reasoning

-- Lax equality of morphisms
module _
  {c c' d d' : Level}
  {C : Container c c'} (D* : LaxContainer d d') where
  
  open Container C renaming (Shape to C₀; Position to C₁)
  module LaxD = LaxContainer D*
  open LaxD
    using ()
    renaming (Carrier to D; S to D₀; P to D₁; _∼_ to _∼₂_)

  record Lax≈ (ff gg : C ⇒ D) : Set (c ⊔ c' ⊔ d ⊔ d') where
    constructor mkLax≈

    open _⇒_ ff renaming (shape to f; position to f#)
    open _⇒_ gg renaming (shape to g; position to g#)
    
    field
      shape : ∀ (c : C₀) → f c ∼₂ g c
      position : ∀ (c : C₀) (pd : D₁ (f c))
        → f# pd ≡ g# (LaxD.subst (shape c) pd)
  
  -- Strict equality implies lax equality
  ≈⊆Lax≈ : ∀ {ff gg} → ff ≈ gg → Lax≈ ff gg
  ≈⊆Lax≈ {ff = f ▷ f#} {gg = g ▷ g#} (mk≈ eqS eqP)
      = mkLax≈ eqS' eqP'
    where
      eqS' : (c : C₀) → f c ∼₂ g c
      eqS' c = LaxD.reflexive (eqS c)

      eqP' : (c : C₀) (pd : D₁ (f c))
        → f# pd ≡ g# (LaxD.subst (eqS' c) pd)
      eqP' c pd = ≡.trans (eqP c pd) (≡.cong g# (props.subst-reflexive D* (eqS c)))

  private
    refl : ∀ {ff} → Lax≈ ff ff
    refl {ff = f ▷ f#} = mkLax≈ (λ _ → LaxD.refl) (λ _ _ → ≡.cong f# LaxD.subst-refl)

    trans : ∀ {ff gg hh} → Lax≈ ff gg → Lax≈ gg hh → Lax≈ ff hh
    trans {ff = f ▷ f#} {gg = g ▷ g#} {hh = h ▷ h#}
      (mkLax≈ f∼g f#≗g#) (mkLax≈ g∼h g#≗h#) = mkLax≈ f∼h f#≗h#
      where
        f∼h : (c : C₀) → f c ∼₂ h c
        f∼h c = LaxD.trans (f∼g c) (g∼h c)

        f#≗h# : (c : C₀) (pd : D₁ (f c))
          → f# pd ≡ h# (LaxD.subst (f∼h c) pd)
        f#≗h# c pd =
          begin
            f# pd
          ≡⟨ f#≗g# c pd ⟩
            g# (LaxD.subst (f∼g c) pd)
          ≡⟨ g#≗h# c (LaxD.subst (f∼g c) pd) ⟩
            h# (LaxD.subst (g∼h c) (LaxD.subst (f∼g c) pd))
          ≡⟨ ≡.cong h# (LaxD.subst-subst (f∼g c)) ⟩
            h# (LaxD.subst (LaxD.trans (f∼g c) (g∼h c)) pd)
          ≡⟨⟩
            h# (LaxD.subst (f∼h c) pd)
          ∎
          where open ≡.≡-Reasoning

    sym : ∀ {ff gg} → Lax≈ ff gg → Lax≈ gg ff
    sym {ff = f ▷ f#} {gg = g ▷ g#} (mkLax≈ f∼g f#≗g#) = mkLax≈ g∼f g#≗f#
      where
        g∼f : (c : C₀) → g c ∼₂ f c
        g∼f c = LaxD.sym (f∼g c)

        g#≗f# : (c : C₀) (pd : D₁ (g c))
          → g# pd ≡ f# (LaxD.subst (g∼f c) pd)
        g#≗f# c pd =
          begin
            g# pd
          ≡⟨ ≡.cong g# (LaxD.subst-subst-sym (f∼g c)) ⟨
            g# (LaxD.subst (f∼g c) (LaxD.subst (g∼f c) pd))
          ≡⟨ f#≗g# c _ ⟨
            f# (LaxD.subst (g∼f c) pd)
          ∎
          where open ≡.≡-Reasoning

  instance
    Lax≈-isEquivalence : IsEquivalence Lax≈
    Lax≈-isEquivalence = record { refl = refl; trans = trans; sym = sym }
  
  Lax≈-setoid : Setoid _ _
  Lax≈-setoid = record {isEquivalence = Lax≈-isEquivalence}

-- When the codomain is strict, "lax" equality is strict equality
-- in disguise
unLax≈ :
  {c c' d d' : Level}
  {C : Container c c'} {D : Container d d'}
  {ff gg : C ⇒ D}
  → (Lax≈ (strict D) ff gg) → ff ≈ gg
unLax≈ (mkLax≈ eqS eqP) = mk≈ eqS eqP

-- Morphism composition ∘ is congruent w.r.t. Lax equivalence
module _
  {c c' d d' e e' : Level}
  {C* : LaxContainer c c'} {D* : LaxContainer d d'} {E* : LaxContainer e e'}
  where

  private
    module LC = LaxContainer C*
    module LD = LaxContainer D*
    module LE = LaxContainer E*
  
  open LC using () renaming (_∼_ to _∼₁_; S to C₀)
  open LE using () renaming (_∼_ to _∼₃_; P to E₁)

  ∘-cong₁-lax :
    {ff₁ ff₂ : ⌊ D* ⌋ ⇒ ⌊ E* ⌋} (_ : Lax≈ E* ff₁ ff₂)
    (gg : ⌊ C* ⌋ ⇒ ⌊ D* ⌋)
    → Lax≈ E* (ff₁ ∘ gg) (ff₂ ∘ gg)
  ∘-cong₁-lax
    (mkLax≈ eqS eqP) (g ▷ g#)
      = mkLax≈ (λ x → eqS (g x)) (λ x pe → ≡.cong g# (eqP (g x) pe))

  -- congruence of postcomposition need
  -- WellDefined
  ∘-cong₂-lax :
    {ff : ⌊ D* ⌋ ⇒ ⌊ E* ⌋} (_ : WellDefined D* E* ff)
    {gg₁ gg₂ : ⌊ C* ⌋ ⇒ ⌊ D* ⌋} (_ : Lax≈ D* gg₁ gg₂)
    → Lax≈ E* (ff ∘ gg₁) (ff ∘ gg₂)
  ∘-cong₂-lax
    {ff = f ▷ f#} well-ff
    {gg₁ = g₁ ▷ g₁#} {gg₂ = g₂ ▷ g₂#} (mkLax≈ eqS eqP) = mkLax≈ eqS' eqP'
    where
      module Wff = WellDefined well-ff
      
      eqS' : (x : C₀) → f (g₁ x) ∼₃ f (g₂ x)
      eqS' x = Wff.shape-cong (eqS x)

      eqP' : (x : C₀) (pe : E₁ (f (g₁ x)))
        → g₁# (f# pe) ≡ g₂# (f# (LE.subst (eqS' x) pe))
      eqP' x pe = ≡.trans (eqP x (f# pe)) (≡.cong g₂# (Wff.position-cong (eqS x))) 