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
import Relation.Binary.Reasoning.Setoid as Reasoning
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_; _≗_)

open import Data.Container.Core

import Container.Morphism.Equality as MorphismEq
open import Container.Morphism.Iso using (_⇔_; mk⇔)

open import Container.Combinator.Tensor

open import Effect.Functor.Day using (Day; day)

open IsEquivalence {{...}}

-- Relation to the Day convolution of interpreted Functors
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

subst-×₁ : ∀ {s p c}
  {S : Set s} (P : S → Set p)
  {C : Set c} (y : C)
  {s₁ s₂ : S} {p₁ : P s₁}
  (eq : s₁ ≡ s₂)
  → ≡.subst (λ s → P s × C) eq (p₁ , y)
     ≡ (≡.subst P eq p₁ , y)
subst-×₁ P y = ≡.subst-application′ P (λ _ → (_, y))

module _ {c₁ c₁' c₂ c₂' d d'}
  {C₁ : Container c₁ c₁'} {C₂ : Container c₂ c₂'} {D : Container d d'} where
  open import Data.Container.Morphism using (_∘_)
  open MorphismEq using (_≈_; mk≈)

  map₁-swap : ∀ {ff : C₁ ⇒ C₂} → map₁ {D = D} ff ∘ swap ≈ swap ∘ map₂ {C = D} ff
  map₁-swap = refl

module _ {c₁ c₁' c₂ c₂' d d'}
  {C₁ : Container c₁ c₁'} {C₂ : Container c₂ c₂'} {D : Container d d'} where
  open Container C₁ renaming (Shape to S₁; Position to P₁) 
  open Container C₂ renaming (Shape to S₂; Position to P₂)
  open Container D renaming (Shape to T; Position to Q)
  open MorphismEq
  open import Data.Container.Morphism using (_∘_)

  map₁-cong : ∀ {ff gg : C₁ ⇒ C₂} → (ff ≈ gg) → map₁ {D = D} ff ≈ map₁ gg
  map₁-cong {ff = f ▷ f#} {gg = g ▷ g#} (mk≈ shapeEq posEq) = mk≈ shapeEq' posEq'
    where
      shapeEq' : ∀ (st : S₁ × T) → _
      shapeEq' (s , t) = ≡.cong (_, t) (shapeEq s)

      posEq' : ∀ (st : S₁ × T) (pq : P₂ (f (proj₁ st)) × Q (proj₂ st)) → _
      posEq' (s , t) (p , q) = begin
          (f# {s = s} p , q)
        ≡⟨ ≡.cong (_, q) (posEq s p) ⟩
          (g# (≡.subst P₂ (shapeEq s) p) , q)
        ≡⟨⟩
          Prod.map₁ g# (≡.subst P₂ (shapeEq s) p , q)
        ≡⟨ ≡.cong (Prod.map₁ g#) (subst-×₁ P₂ q (shapeEq s)) ⟨
          Prod.map₁ g# (≡.subst (λ s₂ → P₂ s₂ × Q t) (shapeEq s) (p , q))
        ≡⟨ ≡.cong (Prod.map₁ g#) (≡.subst-∘ {f = (_, t)} (shapeEq s)) ⟩
          Prod.map₁ g# (≡.subst (Position (C₂ ⊗ D)) (shapeEq' (s , t)) (p , q))
        ∎
        where open ≡.≡-Reasoning
  
  map₂-cong : ∀ {ff gg : C₁ ⇒ C₂} → (ff ≈ gg) → map₂ {C = D} ff ≈ map₂ gg
  map₂-cong {ff = ff} {gg = gg} ff≈gg = begin
      map₂ {C = D} ff
    ≈⟨ refl ⟩
      swap ∘ map₁ ff ∘ swap
    ≈⟨ ∘-cong₁ (∘-cong₂ swap (map₁-cong ff≈gg)) swap ⟩
      swap ∘ map₁ gg ∘ swap
    ≈⟨ refl ⟩
      map₂ gg
    ∎
    where open Reasoning ≈-setoid

open _⇔_

-- Associativity

module _ {c c' d d' e e'}
  {C : Container c c'}
  {D : Container d d'}
  {E : Container e e'} where

  assoc⇔ : (C ⊗ D) ⊗ E ⇔ C ⊗ (D ⊗ E)
  assoc⇔ = mk⇔ assocʳ assocˡ refl refl

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

  braid₁ braid₂ : (C ⊗ D) ⊗ E ⇒ D ⊗ (E ⊗ C)
  braid₁ = assocʳ ∘ swap ∘ assocʳ
  braid₂ = map₂ swap ∘ assocʳ ∘ map₁ swap

  symmetric : braid₁ ≈ braid₂
  symmetric = refl

-- Conversion into Comp
module _ where
  open import Container.Combinator.Compose as Comp
    using (Comp)
  open import Data.Container.Relation.Unary.Any
    using () renaming (any to mk◇)
  open import Data.Container.Morphism using (_∘_)
  open import Container.Morphism.Equality using (_≈_)
  
  ⊗⇒Comp : ∀ {c c' d d'} (C : Container c c') (D : Container d d') → C ⊗ D ⇒ Comp C D
  ⊗⇒Comp _ _ .shape (c , d) = c , λ _ → d
  ⊗⇒Comp _ _ .position {s = c , d} (mk◇ (pc , pd)) = pc , pd

  -- Note: `⊗⇒Comp C D` is neither mono nor epi in general
  -- (but *sometimes* it is, depending on the choice of C and D)

  module _ {c₁ c₁' c₂ c₂' d d'}
    {C₁ : Container c₁ c₁'} {C₂ : Container c₂ c₂'}
    {D : Container d d'} where

    ⊗⇒Comp-nat₁ : (α : C₁ ⇒ C₂) → ⊗⇒Comp C₂ D ∘ map₁ α ≈ Comp.map₁ α ∘ ⊗⇒Comp C₁ D
    ⊗⇒Comp-nat₁ _ = refl

    ⊗⇒Comp-nat₂ : (β : C₁ ⇒ C₂) → ⊗⇒Comp D C₂ ∘ map₂ β ≈ Comp.map₂ β ∘ ⊗⇒Comp D C₁
    ⊗⇒Comp-nat₂ _ = refl