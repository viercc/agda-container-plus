{-# OPTIONS --without-K --safe #-}

module Container.Effect.Functor.Lax where

open import Level

import Function as F

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; _≗_)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Data.Product as Prod using (proj₁; proj₂; _,_)

open import Data.Container.Core
import Data.Container.Properties as ContProp
import Data.Container.Relation.Binary.Equality.Setoid as CEq
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise)
  renaming (_,_ to mkEq)
  public

open import Effect.Functor
open import Effect.Functor.Law

open import Container.Lax
import Container.Effect.Functor as Strict

private
  variable
    s p ℓ : Level

module LaxEquality (C* : LaxContainer s p) (A* : Setoid ℓ ℓ) where
  private
    module LC = LaxContainer C*
  open LC using (S; P; _∼_) renaming (Carrier to C)
  open Setoid A* using () renaming (Carrier to A; _≈_ to _∼ₐ_)

  private
    FA : Set (s ⊔ p ⊔ ℓ)
    FA = ⟦ C ⟧ A

  record LaxEq (cx cy : FA) : Set (s ⊔ p ⊔ ℓ) where
    constructor mkLaxEq
    private
      s₀ = proj₁ cx
      s₁ = proj₁ cy
    field
      shapeEq : s₀ ∼ s₁
      positionEq : ∀ (p : P s₀) → proj₂ cx p ∼ₐ proj₂ cy (LC.subst shapeEq p) 
  
  refl : ∀ {cx} → LaxEq cx cx
  refl {cx = s , v} = mkLaxEq LC.refl (λ _ → Setoid.reflexive A* (≡.cong v LC.subst-refl))

  trans : ∀ {cx cy cz} → LaxEq cx cy → LaxEq cy cz → LaxEq cx cz
  trans {cx = sx , vx } {cy = sy , vy} {cz = sz , vz}
    (mkLaxEq sx∼sy posEq-xy) (mkLaxEq sy∼sz posEq-yz) = mkLaxEq sx∼sz posEq-xz
    where
      sx∼sz : sx ∼ sz
      sx∼sz = LC.trans sx∼sy sy∼sz

      posEq-xz : ∀ (p : P sx) → vx p ∼ₐ vz (LC.subst sx∼sz p)
      posEq-xz p =
        begin
          vx p
        ≈⟨ posEq-xy _ ⟩
          vy (LC.subst sx∼sy p)
        ≈⟨ posEq-yz _ ⟩
          vz (LC.subst sy∼sz (LC.subst sx∼sy p))
        ≈⟨ Setoid.reflexive A* (≡.cong vz (LC.subst-subst sx∼sy)) ⟩
          vz (LC.subst sx∼sz p)
        ∎
        where open Reasoning A*
  
  sym : ∀ {cx cy} → LaxEq cx cy → LaxEq cy cx
  sym {cx = sx , vx } {cy = sy , vy} (mkLaxEq eq posEq)
    = mkLaxEq eq⁻ posEq⁻
    where
      eq⁻ : sy ∼ sx
      eq⁻ = LC.sym eq

      posEq⁻ : ∀ (p : P sy) → vy p ∼ₐ vx (LC.subst (LC.sym eq) p)
      posEq⁻ p =
        begin
          vy p
        ≈⟨ Setoid.reflexive A* (≡.cong vy (LC.subst-subst-sym eq)) ⟨
          vy (LC.subst eq (LC.subst eq⁻ p))
        ≈⟨ posEq (LC.subst eq⁻ p) ⟨
          vx (LC.subst eq⁻ p)
        ∎
        where open Reasoning A*

  instance
    isEquivalence : IsEquivalence LaxEq
    isEquivalence = record {
        refl = refl;
        trans = trans;
        sym = sym
      }
  
  setoid : Setoid (s ⊔ p ⊔ ℓ) (s ⊔ p ⊔ ℓ)
  setoid = record { isEquivalence = isEquivalence}

open LaxEquality using (mkLaxEq) public
open LaxEquality using (LaxEq)

-- Eq defined in the stdlib
-- (Data.Container.Relation.Binary.Equality.Setoid)
-- is a special case of LaxEq where the container is
-- strict.

toEq : ∀ {s p a} {C : Container s p} {A* : Setoid a a}
  → ∀ {cx cy} → LaxEq (strict C) A* cx cy → CEq.Eq A* C cx cy
toEq (mkLaxEq shapeEq positionEq) = mkEq shapeEq positionEq

fromEq : ∀ {s p a} {C : Container s p} {A* : Setoid a a}
  → ∀ {cx cy} → CEq.Eq A* C cx cy → LaxEq (strict C) A* cx cy
fromEq (mkEq shapeEq positionEq) = mkLaxEq shapeEq positionEq

module _ (C* : LaxContainer s p) where
  private
    module LC = LaxContainer C*
  open LC using (S; P; _∼_) renaming (Carrier to C)

  private
    LaxEq-≡ : ∀ {x} {X : Set x} → Rel (⟦ C ⟧ X) (s ⊔ p ⊔ x)
    LaxEq-≡ {X = X} = LaxEq C* (≡.setoid X)

    instance
      LaxEq-≡-isEquivalence : ∀ {x} {X : Set x} → IsEquivalence (LaxEq-≡ {X = X})
      LaxEq-≡-isEquivalence {X = X} = LaxEquality.isEquivalence C* (≡.setoid X)
 
    module isFunctor (ℓ : Level) where
      F : Set ℓ → Set (s ⊔ p ⊔ ℓ)
      F = ⟦ C ⟧

      infix 3 _≈_
      _≈_ : ∀ {X} → Rel (F X) _
      _≈_ = LaxEq-≡

      open RawFunctor (Strict.makeRawFunctor C ℓ)

      <$>-cong : ∀ {A B : Set ℓ} (f : A → B) {u₁ u₂ : F A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
      <$>-cong f (mkLaxEq eqS eqV) = mkLaxEq eqS (λ p → ≡.cong f (eqV p))
      
      <$>-id : ∀ {A : Set ℓ} (x : F A) → (F.id <$> x ≈ x)
      <$>-id (_ , v) = mkLaxEq LC.refl (λ _ → ≡.cong v LC.subst-refl)

      <$>-∘  : ∀ {A B C : Set ℓ} (f : B → C) (g : A → B) (x : F A)
        → (f <$> (g <$> x) ≈ (f F.∘′ g) <$> x)
      <$>-∘ f g (_ , v) = mkLaxEq LC.refl (λ _ → ≡.cong (f F.∘′ g F.∘′ v) LC.subst-refl)

  makeIsFunctorLaxly : (e : Level) → IsFunctor {ℓ = e} ⟦ C ⟧ LaxEq-≡ (Strict.makeRawFunctor C e)
  makeIsFunctorLaxly e = record { isFunctor e }
 
  makeFunctorLaxly : (e : Level) → Functor {ℓ = e} ⟦ C ⟧ LaxEq-≡
  makeFunctorLaxly e = record { isFunctor = makeIsFunctorLaxly e }
