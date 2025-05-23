{-# OPTIONS --without-K --safe #-}

module Container.Morphism.Equality where

open import Level

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

import Function as F
open F using (id; _∘_)
import Data.Product as Prod
open Prod using (Σ; _,_)
open import Data.Product.Properties
  using (Σ-≡,≡←≡)

open import Data.Container.Core
import Data.Container.Relation.Binary.Equality.Setoid as CEq
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise)
  renaming (_,_ to mkPointwise)

private
  module _ {a} {A : Set a} {b} {B : A → Set b} {c} {C : Set c} where
    sym-subst : {x y : A} → (eq : x ≡ y)
      → {f : B x → C} {g : B y → C}
      → (∀ (bx : B x) → f bx ≡ g (≡.subst B eq bx))
      → (∀ (by : B y) → g by ≡ f (≡.subst B (≡.sym eq) by))
    sym-subst ≡.refl f≗g by = ≡.sym (f≗g by)
  
  module _ {a} {A : Set a} {b} {B : A → Set b} {c} {C : Set c} where
    subst-contramap : {x y : A} → (eq : x ≡ y)
      → {f : B x → C} {g : B y → C}
      → (≡.subst (λ z → (B z → C)) eq f ≡ g)
      → ∀ (bx : B x) → f bx ≡ g (≡.subst B eq bx)
    subst-contramap ≡.refl ≡.refl _ = ≡.refl

module _ {s₁ p₁ s₂ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} where
  infix 4 _≈_

  record _≈_ (ff gg : C₁ ⇒ C₂) : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
    constructor mk≈

    open Container C₁ renaming (Shape to S₁; Position to P₁)
    open Container C₂ renaming (Shape to S₂; Position to P₂)

    open _⇒_ ff renaming
      (shape to f; position to f#)
    open _⇒_ gg renaming
      (shape to g; position to g#)
    
    field shape    : f ≗ g
          position : ∀ (c : S₁) → f# {c} ≗ g# {c} ∘ ≡.subst P₂ (shape c)
  
  open _≈_
  
  private
    refl : {m : C₁ ⇒ C₂} → m ≈ m
    refl = mk≈ (λ _ → ≡.refl) (λ _ _ → ≡.refl)

    sym : {m n : C₁ ⇒ C₂} → m ≈ n → n ≈ m
    sym m≈n =
      mk≈ (λ c → ≡.sym (m≈n .shape c)) 
          (λ c p → sym-subst (m≈n .shape c) (m≈n .position c) p)
    
    trans : {m n r : C₁ ⇒ C₂} → m ≈ n → n ≈ r → m ≈ r
    trans {m = m ▷ m#} {n = n ▷ n#} {r = r ▷ r#} m≈n n≈r = mk≈ shape≈ pos≈
      where
        S₁ = Shape C₁
        P₂ = Position C₂
        shape≈ : (c : S₁) → m c ≡ r c
        shape≈ c = ≡.trans (shape m≈n c) (shape n≈r c)

        pos≈ : (c : S₁) (p : P₂ (m c)) → m# p ≡ r# (≡.subst P₂ (shape≈ c) p)
        pos≈ c p =
          begin
            m# p
          ≡⟨ position m≈n c p ⟩
            n# (≡.subst P₂ (shape m≈n c) p)
          ≡⟨ position n≈r c _ ⟩
            r# (≡.subst P₂ (shape n≈r c) (≡.subst P₂ (shape m≈n c) p))
          ≡⟨ ≡.cong r# (≡.subst-subst (shape m≈n c)) ⟩
            r# (≡.subst P₂ (shape≈ c) p)
          ∎
          where open ≡.≡-Reasoning
  
  instance
    isEquivalence : IsEquivalence _≈_
    isEquivalence =
      record { refl = refl; sym = sym; trans = trans }
  
  ≈-setoid : Setoid (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂)
  ≈-setoid = record { isEquivalence = isEquivalence }

module _ {s₁ p₁ s₂ p₂ s₃ p₃}
  {C₁ : Container s₁ p₁}
  {C₂ : Container s₂ p₂}
  {C₃ : Container s₃ p₃} where
  import Data.Container.Morphism as CM

  ∘-cong₁ : {α₁ α₂ : C₂ ⇒ C₃} (_ : α₁ ≈ α₂) (β : C₁ ⇒ C₂) → α₁ CM.∘ β ≈ α₂ CM.∘ β
  ∘-cong₁ (mk≈ shapeα posα) (g ▷ g#) =
    mk≈ (λ c₁ → shapeα (g c₁)) (λ c₁ p₃ → ≡.cong g# (posα (g c₁) p₃))
  
  ∘-cong₂ : (α : C₂ ⇒ C₃) {β₁ β₂ : C₁ ⇒ C₂} (_ : β₁ ≈ β₂) → α CM.∘ β₁ ≈ α CM.∘ β₂
  ∘-cong₂
    (f ▷ f#)
    {β₁ = g₁ ▷ g₁#} {β₂ = g₂ ▷ g₂#} (mk≈ shapeβ posβ)
      = mk≈ eqS eqP
    where
      open Container C₁ renaming (Shape to S₁; Position to P₁)
      open Container C₂ renaming (Shape to S₂; Position to P₂)
      open Container C₃ renaming (Shape to S₃; Position to P₃)

      eqS : (c₁ : S₁) → f (g₁ c₁) ≡ f (g₂ c₁)
      eqS c₁ = ≡.cong f (shapeβ c₁)

      f#' : (c₂ : S₂) → P₃ (f c₂) → P₂ c₂
      f#' c₂ = f# {c₂}

      eqP : (c : S₁) (p₃ : P₃ (f (g₁ c)))
        → g₁# (f# p₃) ≡ g₂# (f# (≡.subst P₃ (eqS c) p₃))
      eqP c p₃ = begin
          g₁# (f# p₃)
        ≡⟨ posβ c (f# p₃) ⟩
          g₂# (≡.subst P₂ eq (f# p₃))
        ≡⟨⟩
          g₂# (≡.subst P₂ eq (f#' (g₁ c) p₃))
        ≡⟨ ≡.cong g₂# (≡.subst-application P₃ {B₂ = P₂} {f = f} f#' eq) ⟩
          g₂# (f#' (g₂ c) (≡.subst P₃ (≡.cong f eq) p₃))
        ≡⟨⟩
          g₂# (f# (≡.subst P₃ (eqS c) p₃))
        ∎
        where
          eq : g₁ c ≡ g₂ c
          eq = shapeβ c

          open ≡.≡-Reasoning

module _ {s₁ p₁ s₂ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where
  -- Variant of _≈_ taking C₁, C₂ as explicit argument
  Eq : Rel (C₁ ⇒ C₂) (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂)
  Eq = _≈_ {C₁ = C₁} {C₂ = C₂}

module ≈-correctness {s₁ p₁ s₂ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂) where
  open Container C₁ renaming (Shape to S₁; Position to P₁)
  open Container C₂ renaming (Shape to S₂; Position to P₂)
  
  module _ {s p} (C : Container s p) {x} {X : Set x} where
    open import Relation.Binary.Core using (Rel)
    
    -- Pointwise equality between ⟦_⟧
    Eq⟦⟧ : Rel (⟦ C ⟧ X) (s ⊔ p ⊔ x)
    Eq⟦⟧ = CEq.Eq (≡.setoid X) C
  
  -- Pointwise Eq⟦⟧ on ⟪⟫
  Eq⟪⟫ : ∀ (ff gg : C₁ ⇒ C₂) {x} {X : Set x} → Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂ ⊔ x)
  Eq⟪⟫ ff gg {X = X} = ∀ (xs : ⟦ C₁ ⟧ X) → Eq⟦⟧ C₂ (⟪ ff ⟫ xs) (⟪ gg ⟫ xs)

  -- Pointwise ≡ on ⟪⟫
  ≡⟪⟫ : ∀ (ff gg : C₁ ⇒ C₂) {x} {X : Set x}  → Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂ ⊔ x)
  ≡⟪⟫ ff gg {X = X} = ∀ (xs : ⟦ C₁ ⟧ X) → ⟪ ff ⟫ xs ≡ ⟪ gg ⟫ xs

  -- Pointwise ≡ implies Pointwise Eq⟦⟧
  ≡⟪⟫→Eq⟪⟫ : ∀ {ff gg : C₁ ⇒ C₂} {x} {X : Set x} → ≡⟪⟫ ff gg {X = X} → Eq⟪⟫ ff gg {X = X}
  ≡⟪⟫→Eq⟪⟫ {ff} {gg} {X = X} ff≡⟪⟫gg xs
      with Σ-≡,≡←≡ (ff≡⟪⟫gg xs)
  ... | eqShape , eqValues = eq
    where
      eq : Eq⟦⟧ C₂ (⟪ ff ⟫ xs) (⟪ gg ⟫ xs)
      eq .Pointwise.shape    = eqShape
      eq .Pointwise.position = subst-contramap eqShape eqValues

  -- Because Eq⟪⟫ has unbounded level, it can't be used as a type.
  -- Eq⟪⟫' is a restricted version of Eq⟪⟫ which has just enough
  -- polymorphism necessary to get ≈ out of it.
  Eq⟪⟫' : ∀ (ff gg : C₁ ⇒ C₂) → Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂)
  Eq⟪⟫' ff gg = ∀ {c : S₁} → Eq⟪⟫ ff gg {X = P₁ c}
  
  -- ==== Pointwise Eq⟦⟧ on ⟪⟫ ↔ Container equality _≈_

  -- == ­→ direction

  Eq⟪⟫'→≈ : ∀ {ff gg : C₁ ⇒ C₂}
    → Eq⟪⟫' ff gg → ff ≈ gg
  Eq⟪⟫'→≈ {ff} {gg} equiv = mk≈ shape≈ position≈
    where
      open _⇒_ ff renaming
        (shape to f; position to f#)
      open _⇒_ gg renaming
        (shape to g; position to g#)
      
      shape≈ : ∀ (c : S₁) → f c ≡ g c
      shape≈ c = equiv (c , id) .Pointwise.shape

      position≈ : ∀ (c : S₁) (p : P₂ (f c)) → f# {c} p ≡ g# {c} (≡.subst P₂ (shape≈ c) p)
      position≈ c = equiv (c , id) .Pointwise.position
  
  -- == ­← direction

  ≈→Eq⟪⟫ : ∀ {ff gg : C₁ ⇒ C₂}
    → ff ≈ gg
    → ∀ {x} {X : Set x} → Eq⟪⟫ ff gg {X = X}
  ≈→Eq⟪⟫ {ff} {gg} ff≈gg {X = X} (c , px) = mkPointwise shapeEq positionEq
    where
      open _⇒_ ff renaming
        (shape to f; position to f#)
      open _⇒_ gg renaming
        (shape to g; position to g#)
      open _≈_ ff≈gg renaming
        (shape to shape≈; position to position≈)

      shapeEq : f c ≡ g c
      shapeEq = shape≈ c

      positionEq : ∀ (p : P₂ (f c)) → px (f# {c} p) ≡ px (g# {c} (≡.subst P₂ shapeEq p))
      positionEq p = ≡.cong px (position≈ c p)

  -- ≡⟪⟫ is stronger than Eq⟪⟫, thus → direction can take ≡⟪⟫ instead
  ≡⟪⟫' : ∀ (ff gg : C₁ ⇒ C₂) → Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂)
  ≡⟪⟫' ff gg = ∀ {c : S₁} → ≡⟪⟫ ff gg {X = P₁ c}
  
  ≡⟪⟫'→≈ : ∀ {ff gg : C₁ ⇒ C₂}
    → ≡⟪⟫' ff gg → (ff ≈ gg)
  ≡⟪⟫'→≈ eq = Eq⟪⟫'→≈ (≡⟪⟫→Eq⟪⟫ eq)
