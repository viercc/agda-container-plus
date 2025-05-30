{-# OPTIONS --without-K --safe #-}

-- Properties of container tensor product _⊗_.
-- 
-- * to-⊗ and from-⊗ are isomorphisms between Functors
-- * _⊗_ is Monoidal. All equalities about monoidal hold definitionally.
--   (hence every proof is done by `refl`)
module Container.Combinator.Tensor.Properties where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (_×_; proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

open import Data.Container.Core

import Container.Morphism.Equality using (isEquivalence)
open import Container.Morphism.Iso using (_⇔_; mk⇔)

open import Container.Combinator.Monoidal
open import Container.Combinator.Tensor

open import Effect.Functor.Day using (Day; day)

open IsEquivalence {{...}}

module correct {c c' d d' x} (C : Container c c') (D : Container d d') where
  open Container C renaming (Shape to S₁; Position to P₁)
  open Container D renaming (Shape to S₂; Position to P₂)

  open import Container.Effect.Functor as ConFunctor
  open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)

  private

    F : Set c' → Set (c ⊔ c')
    F = ⟦ C ⟧

    G : Set d' → Set (d ⊔ d')
    G = ⟦ D ⟧

    H : Set x → Set _
    H = ⟦ C ⊗ D ⟧

    functorF = makeFunctor C c'
    functorG = makeFunctor D d'
    functorH = makeFunctor (C ⊗ D) x
    
    open Effect.Functor.Day.Law {x = x} functorF functorG
      renaming (_≈_ to _Day≈_)

    to : ∀ {X} → Day F G X → H X
    to = to-⊗ C D

    from : ∀ {X} → H X → Day F G X
    from = from-⊗ C D

    to-cong-∼ : ∀ {X} {u v : Day F G X} → u ∼ v → to u ≈ to v
    to-cong-∼ (congF op (Pw ≡.refl pos≈-F) gb) =
      Pw ≡.refl λ (pc , pd) → ≡.cong (λ a → op (a , proj₂ gb pd)) (pos≈-F pc)
    to-cong-∼ (congG op fa (Pw ≡.refl pos≈-G)) =
      Pw ≡.refl λ (pc , pd) → ≡.cong (λ b → op (proj₂ fa pc , b)) (pos≈-G pd)
    to-cong-∼ (link linkA linkB op≗ (_ , uf) (_ , ug))
        = Pw ≡.refl (λ (p₁ , p₂) → op≗ (uf p₁ , ug p₂))

    import Relation.Binary.Construct.Closure.Equivalence as ClEq

    to-cong : ∀ {X} {u v : Day F G X} → u Day≈ v → to u ≈ to v
    to-cong = ClEq.gfold ConFunctor.≈-isEquivalence to to-cong-∼

    from-cong : ∀ {X} {hx hy : H X} → hx ≈ hy → from hx Day≈ from hy
    from-cong (Pw ≡.refl pos≈H) = day-link F.id F.id pos≈H

    to-from : ∀ {X} {hx : H X} → to (from hx) ≈ hx
    to-from = refl 

    from-to : ∀ {X} {u : Day F G X} → from (to u) Day≈ u
    from-to {u = day _ fa gb} = day-link (proj₂ fa) (proj₂ gb) (λ _ → ≡.refl)

    inverseˡ : ∀ {X} {x : H X} {y : Day F G X} → y Day≈ from x → to y ≈ x
    inverseˡ eq = trans (to-cong eq) to-from

    inverseʳ : ∀ {X} {x : Day F G X} {y : H X} → y ≈ to x → from y Day≈ x
    inverseʳ eq = trans (from-cong eq) from-to

  correct : {X : Set x} → F.Inverse (Day-setoid X) (≈-setoid {Con = C ⊗ D} X)
  correct = record {
      to-cong = to-cong;
      from-cong = from-cong;
      inverse = inverseˡ , inverseʳ
    }

module _ {c c' d d' : Level} where
  functorial₁ : {D : Container d d'} → Functorial {c = c} {c' = c'} (_⊗ D) map₁
  functorial₁ {D = D} = record {
      map-id = refl;
      map-∘ = λ _ _ → refl
    }

  functorial₂ : {C : Container c c'} → Functorial {c = d} {c' = d'} (C ⊗_) map₂
  functorial₂ {C = C} = record {
      map-id = refl;
      map-∘ = λ _ _ → refl
    }

  bifunctorial : Bifunctorial _⊗_ map₁ map₂
  bifunctorial = record {
      functorial₁ = functorial₁;
      functorial₂ = functorial₂;
      map₁-map₂ = λ _ _ → refl
    }

open _⇔_

-- Associativity

module _ {c c' d d' e e'}
  {C : Container c c'}
  {D : Container d d'}
  {E : Container e e'} where
  assoc⇔ : (C ⊗ D) ⊗ E ⇔ C ⊗ (D ⊗ E)
  assoc⇔ = mk⇔ assocʳ assocˡ refl refl

semigroupal : {c c' : Level} → Semigroupal {c = c} {c' = c'} _⊗_ map₁ map₂ assoc⇔
semigroupal = record {
    bifunctorial = bifunctorial;
    assoc-nat = λ _ _ _ → refl;
    pentagon = refl
  }

-- Units
module _ {c c'} {C : Container c c'} where
  unitLeft⇔ : Id ⊗ C ⇔ C
  unitLeft⇔ = record {
      to = unitLeft; from = ununitLeft;
      to-from = refl;
      from-to = refl
    }

  unitRight⇔ : C ⊗ Id ⇔ C
  unitRight⇔ = record {
      to = unitRight; from = ununitRight;
      to-from = refl;
      from-to = refl
    }

monoidal : {c : Level} → Monoidal {c = c} {c' = c} _⊗_ Id map₁ map₂ assoc⇔ unitLeft⇔ unitRight⇔
monoidal {c} = record {
    semigroupal = semigroupal;
    unitl-nat = λ _ → refl;
    unitr-nat = λ _ → refl;
    unit-unit = refl;
    assoc-unit = refl
  }

module _ {c c' d d'} {C : Container c c'} {D : Container d d'} where
  swap⇔ : C ⊗ D ⇔ D ⊗ C
  swap⇔ = record {
      to = swap;
      from = swap;
      to-from = refl;
      from-to = refl
    }

module _ {c c' d d' e e'} {C : Container c c'} {D : Container d d'} {E : Container e e'} where
  open import Data.Container.Morphism using (_∘_)
  open import Container.Morphism.Equality using (_≈_)

  private
    braid₁ braid₂ : (C ⊗ D) ⊗ E ⇒ D ⊗ (E ⊗ C)
    braid₁ = assocʳ ∘ swap ∘ assocʳ
    braid₂ = map₂ swap ∘ assocʳ ∘ map₁ swap

  symmetric : braid₁ ≈ braid₂
  symmetric = refl

-- Conversion into Comp
module _ {c c' d d'} where
  open import Container.Combinator.Compose as Comp
    using (Comp)
  open import Data.Container.Relation.Unary.Any
    using () renaming (any to mk◇)
  open import Data.Container.Morphism using (_∘_)
  open import Container.Morphism.Equality using (_≈_)
  
  ⊗⇒Comp : (C : Container c c') (D : Container d d') → C ⊗ D ⇒ Comp C D
  ⊗⇒Comp _ _ .shape (c , d) = c , λ _ → d
  ⊗⇒Comp _ _ .position {s = c , d} (mk◇ (pc , pd)) = pc , pd

  -- Note: `⊗⇒Comp C D` is neither mono nor epi in general
  -- (but *sometimes* it is, depending on the choice of C and D)

  ⊗⇒Comp-nat₁ : ∀ {C₁ C₂ : Container c c'} {D : Container d d'}
    → (α : C₁ ⇒ C₂) → ⊗⇒Comp C₂ D ∘ map₁ α ≈ Comp.map₁ α ∘ ⊗⇒Comp C₁ D
  ⊗⇒Comp-nat₁ _ = refl

  ⊗⇒Comp-nat₂ : ∀ {C : Container c c'} {D₁ D₂ : Container d d'}
    → (β : D₁ ⇒ D₂) → ⊗⇒Comp C D₂ ∘ map₂ β ≈ Comp.map₂ β ∘ ⊗⇒Comp C D₁
  ⊗⇒Comp-nat₂ _ = refl