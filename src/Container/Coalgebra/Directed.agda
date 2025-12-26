{-# OPTIONS --without-K --safe #-}

-- Directed containers ≃ "unpacked" Comonads
module Container.Coalgebra.Directed where

open import Level

import Function as F
open F using (_∋_)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Axiom.Extensionality.Propositional
  using (Extensionality; lower-extensionality)

open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
import Data.Product.Properties as ProdProp
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Data.Container.Core renaming (map to map⟦⟧)
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Compose as Compose
  using (Id; Comp; map₁; map₂)

open import Container.Coalgebra.Comonad

private
  variable
    s p : Level

record RawDirected (C : Container s p) : Set (s ⊔ p) where
  open Container C renaming (Shape to S; Position to P) public

  infixr 5 _⊕_

  field
    root : (s : S) → P s
    ↓ : {s : S} → P s → S
    _⊕_ : {s : S} → (p₁ : P s) → P (↓ p₁) → P s

record IsDirected (C : Container s p) (raw : RawDirected C) : Set (s ⊔ p) where
  open RawDirected raw

  field
    ↓-root : {s : S} → ↓ (root s) ≡ s
    ↓-⊕ : {s : S} → (p₁ : P s) → (p₂ : P (↓ p₁)) → ↓ (p₁ ⊕ p₂) ≡ ↓ p₂

    ⊕-root : {s : S} → (p : P s)
      → p ⊕ root (↓ p) ≡ p
    root-⊕ : {s : S} → (p : P (↓ (root s)))
      → root s ⊕ p ≡ ≡.subst P ↓-root p
    ⊕-⊕ : ∀ {s : S} (p₁ : P s) (p₂ : P (↓ p₁)) (p₃ : P (↓ (p₁ ⊕ p₂)))
      → (p₁ ⊕ p₂) ⊕ p₃ ≡ p₁ ⊕ (p₂ ⊕ (≡.subst P (↓-⊕ p₁ p₂) p₃))

record Directed (C : Container s p) : Set (s ⊔ p) where
  field
    rawDirected : RawDirected C
    isDirected : IsDirected C rawDirected
  
  open RawDirected rawDirected public
  open IsDirected isDirected public

module _ {x} (C : Container s p) (funext : Extensionality p x) where
  open Container C renaming (Shape to S; Position to P)
  ⟦⟧-ext : ∀ {X : Set x} {s₁ s₂ : S} (eq-s : s₁ ≡ s₂)
    → {v₁ : P s₁ → X } {v₂ : P s₂ → X} (eq-v : ≡.subst (λ s′ → P s′ → X) eq-s v₁ ≗ v₂)
    → (s₁ , v₁) ≡ (s₂ , v₂)
  ⟦⟧-ext eq-s eq-v = ProdProp.Σ-≡,≡→≡ (eq-s , funext eq-v)

  ⟦⟧-ext′ : ∀ {X : Set x} (s₀ : S)
    → {v₁ v₂ : P s₀ → X } (eq-v : v₁ ≗ v₂)
    → (⟦ C ⟧ X ∋ (s₀ , v₁)) ≡ (s₀ , v₂)
  ⟦⟧-ext′ s₀ eq-v = ≡.cong (s₀ ,_) (funext eq-v)

module _ {C : Container s p} where
  packRaw : RawDirected C → RawComonad C
  packRaw raw = record { extract = ext; duplicate = dup } 
    where
      open RawDirected raw
      ext : C ⇒ Id
      ext = F.const tt ▷ λ {s} _ → root s

      dup : C ⇒ Comp C C
      dup = (λ s → s , ↓) ▷ (λ {_} (mk◇ (p₁ , p₂)) → p₁ ⊕ p₂)

  packLaw : (raw : RawDirected C) → IsDirected C raw → IsComonad C (packRaw raw)
  packLaw raw law = record {
    left-unit = left-unit';
    right-unit = right-unit';
    assoc = assoc'
    }
    where
      open RawDirected raw
      open IsDirected law
      open RawComonad (packRaw raw)
      
      left-unit' : unitLeft ∘ map₁ extract ∘ duplicate ≈ id C
      left-unit' = mk≈ (λ _ → ↓-root) (λ _ → root-⊕)

      right-unit' : unitRight ∘ map₂ extract ∘ duplicate ≈ id C
      right-unit' = mk≈ (λ _ → ≡.refl) (λ _ → ⊕-root)

      -- Can't be proved because funext is necessary!
      assoc' : assocʳ ∘ map₁ duplicate ∘ duplicate ≈ map₂ duplicate ∘ duplicate
      assoc' = _

  pack : Directed C → Comonad C
  pack dir = record { rawComonad = raw'; isComonad = law' }
    where
      raw' = packRaw (Directed.rawDirected dir)
      law' = packLaw _ (Directed.isDirected dir)

  subst-f : ∀ {a b} {A : Set a} (B : A → Set b) (f : (x : A) → B x)
    → {x₁ x₂ : A} → (eq : x₁ ≡ x₂) → ≡.subst B eq (f x₁) ≡ f x₂
  subst-f B f ≡.refl = ≡.refl

  -- Unlike Monad <-> Uustalu.Monad,
  -- unpacking direction depends on Comonad laws, thus
  -- no unpackRaw.
  unpack : UIP (Shape C) → Comonad C → Directed C
  unpack isSetS comonad = record { rawDirected = raw'; isDirected = law' }
    where
      open Container C renaming (Shape to S; Position to P)
      open Comonad comonad

      C⟦⟧-injectiveʳ : ∀ {ℓ} {X : Set ℓ} {s₁ : S} {v₁ v₂ : P s₁ → X}
        → (⟦ C ⟧ X ∋ (s₁ , v₁)) ≡ (s₁ , v₂) → v₁ ≡ v₂
      C⟦⟧-injectiveʳ eq = ProdProp.,-injectiveʳ-UIP isSetS eq

      elim-subst-P : ∀ {s₁ : S} {eq : s₁ ≡ s₁} {p : P s₁}
        → ≡.subst P eq p ≡ p
      elim-subst-P {eq = eq} {p = p} = ≡.cong (λ eq′ → ≡.subst P eq′ p) (isSetS eq ≡.refl)

      root : (s : S) → P s
      root s = _⇒_.position extract {s} tt

      s₁-id : {s : S} → proj₁ (_⇒_.shape duplicate s) ≡ s
      s₁-id {s} = _≈_.shape right-unit s

      to-s₁ : {s : S} → P s → P (proj₁ (_⇒_.shape duplicate s))
      to-s₁ = ≡.subst P (≡.sym s₁-id)

      ↓ : {s : S} → P s → S
      ↓ {s} = ≡.subst (λ s′ → P s′ → S) s₁-id
        (_⇒_.shape duplicate s .proj₂)

      dup-shape : (s : S) → ⟦ C ⟧ S
      dup-shape s = (s , ↓)

      is-dup-shape : (s : S) → _⇒_.shape duplicate s ≡ dup-shape s
      is-dup-shape s = ProdProp.Σ-≡,≡→≡ (s₁-id , ≡.refl)
      
      dup-position : {s : S} → ◇ C P (dup-shape s) → P s
      dup-position {s} = 
        _⇒_.position duplicate F.∘ ≡.subst (◇ C P) (≡.sym (is-dup-shape s))
      
      _⊕_ : {s : S} → (p₁ : P s) → P (↓ p₁) → P s
      _⊕_ {s} p₁ p₂ = dup-position (mk◇ (p₁ , p₂))

      dup : C ⇒ Comp C C
      dup .shape = dup-shape
      dup .position = dup-position

      is-dup : duplicate ≈ dup
      is-dup = mk≈ is-dup-shape λ s p →
        ≡.cong (duplicate .position)
          (≡.sym (≡.subst-sym-subst (is-dup-shape s)))

      left-unit' : unitLeft ∘ map₁ extract ∘ dup ≈ id C
      left-unit' = begin
          unitLeft ∘ map₁ extract ∘ dup
        ≈⟨ ∘-cong₂ (unitLeft ∘ map₁ {C = C} extract) is-dup ⟨
          unitLeft ∘ map₁ extract ∘ duplicate
        ≈⟨ left-unit ⟩
          id C
        ∎
        where open Reasoning ≈-setoid
      
      right-unit' : unitRight ∘ map₂ extract ∘ dup ≈ id C
      right-unit' = begin
          unitRight ∘ map₂ extract ∘ dup
        ≈⟨ ∘-cong₂ (unitRight ∘ map₂ {C = C} extract) is-dup ⟨
          unitRight ∘ map₂ extract ∘ duplicate
        ≈⟨ right-unit ⟩
          id C
        ∎
        where open Reasoning ≈-setoid

      assoc' : assocʳ ∘ map₁ dup ∘ dup ≈ map₂ dup ∘ dup
      assoc' = _
      
      ↓-root : {s : S} → ↓ (root s) ≡ s
      ↓-root {s} = left-unit' ._≈_.shape s

      ↓-⊕ : {s : S} → (p₁ : P s) → (p₂ : P (↓ p₁)) → ↓ (p₁ ⊕ p₂) ≡ ↓ p₂
      ↓-⊕ {s} p₁ p₂ = _

      ⊕-root : {s : S} → (p : P s)
        → p ⊕ root (↓ p) ≡ p
      ⊕-root {s} p = ≡.trans
        (right-unit' ._≈_.position s p)
        elim-subst-P

      root-⊕ : {s : S} → (p : P (↓ (root s)))
        → root s ⊕ p ≡ ≡.subst P ↓-root p
      root-⊕ {s} p = left-unit' ._≈_.position s p

      ⊕-⊕ : ∀ {s : S} (p₁ : P s) (p₂ : P (↓ p₁)) (p₃ : P (↓ (p₁ ⊕ p₂)))
        → (p₁ ⊕ p₂) ⊕ p₃ ≡ p₁ ⊕ (p₂ ⊕ (≡.subst P (↓-⊕ p₁ p₂) p₃))
      ⊕-⊕ {s} p₁ p₂ p₃ = _

      raw' : RawDirected C
      raw' = record { root = root ; ↓ = ↓ ; _⊕_ = _⊕_ }

      law' : IsDirected C raw'
      law' = record {
        ↓-root = ↓-root;
        ↓-⊕ = ↓-⊕;
        root-⊕ = root-⊕;
        ⊕-root = ⊕-root;
        ⊕-⊕ = ⊕-⊕ }