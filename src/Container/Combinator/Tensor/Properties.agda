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
open ≡ using (_≡_)

open import Data.Container.Core

import Container.Morphism.Equality using (isEquivalence)
open import Container.Morphism.Iso using (_⇔_; mk⇔)

open import Container.Combinator.Monoidal
open import Container.Combinator.Tensor

open import Effect.Functor.Day using (Day)

private
  variable
    c c' d d' e e' f f' : Level

open IsEquivalence {{...}}

module correct {c c' d d' x} (C : Container c c') (D : Container d d') where
  open Container C renaming (Shape to S₁; Position to P₁)
  open Container D renaming (Shape to S₂; Position to P₂)

  open import Container.Effect.Functor
  open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)

  private
    module DayM = Effect.Functor.Day

    F : Set c' → Set (c ⊔ c')
    F = ⟦ C ⟧

    G : Set d' → Set (d ⊔ d')
    G = ⟦ D ⟧

    H : Set x → Set _
    H = ⟦ C ⊗ D ⟧

    functorF = makeFunctor C c'
    functorG = makeFunctor D d'
    functorH = makeFunctor (C ⊗ D) x
    
    Day-setoid : ∀ (X : Set x) → Setoid _ _
    Day-setoid X = DayM.Day-setoid functorF functorG X

    module _ {X : Set x} where
      open Setoid (Day-setoid X) using ()
        renaming (isEquivalence to isEquivalenceDay; _≈_ to _Day≈_) public
      
      instance
        isEquivalenceDay' : IsEquivalence _Day≈_
        isEquivalenceDay' = isEquivalenceDay

    to : ∀ {X} → Day F G X → H X
    to = to-⊗ C D

    from : ∀ {X} → H X → Day F G X
    from = from-⊗ C D
    
    _⊏_ : ∀ {X : Set x} → Rel (Day F G X) _
    _⊏_ = DayM._⊏_ functorF functorG

    open DayM using (day)

    to-cong-⊏ : ∀ {X} {u v : Day F G X} → u ⊏ v → to u ≈ to v
    to-cong-⊏
      {u = day _ _ op _ gb }
        (DayM.congF (Pw ≡.refl pos≈-F)) = Pw ≡.refl λ (pc , pd) → ≡.cong (λ a → op (a , proj₂ gb pd)) (pos≈-F pc)
    to-cong-⊏
      {u = day _ _ op fa _ }
        (DayM.congG (Pw ≡.refl pos≈-G)) = Pw ≡.refl λ (pc , pd) → ≡.cong (λ b → op (proj₂ fa pc , b)) (pos≈-G pd)
    to-cong-⊏
       {u = day _ _  op  (c , uf) (d , ug)}
       {v = day _ _  op' (_ , vf) (_ , vg)}
       (DayM.link linkA linkB op≗)
        = Pw ≡.refl pos≈
      where
        pos≈ : (pp : P₁ c × P₂ d)
          → (let p₁ , p₂ = pp)
          → op (uf p₁ , ug p₂) ≡ op' (vf p₁ , vg p₂)
        pos≈ (p₁ , p₂) =
          begin
            op (uf p₁ , ug p₂)
          ≡⟨ op≗ _ ⟩
            op' (Prod.map linkA linkB (uf p₁ , ug p₂))
          ≡⟨⟩
            op' (linkA (uf p₁) , linkB (ug p₂))
          ≡⟨⟩
            op' (vf p₁ , vg p₂)
          ∎
          where open ≡.≡-Reasoning

    import Relation.Binary.Construct.Closure.Equivalence as ClEq

    to-cong : ∀ {X} {u v : Day F G X} → u Day≈ v → to u ≈ to v
    to-cong = ClEq.gfold ≈-isEquivalence to to-cong-⊏

    from-cong : ∀ {X} {hx hy : H X} → hx ≈ hy → from hx Day≈ from hy
    from-cong
      { hx = hx@((c , d) , h₁) }
      { hy = hy@(_       , h₂) }
      ( Pw ≡.refl pos≈H ) = ClEq.return proof
      where
        proof : from hx ⊏ from hy
        proof = DayM.link F.id F.id pos≈H

    to-from : ∀ {X} {hx : H X} → to (from hx) ≈ hx
    to-from = refl 

    from-to : ∀ {X} {u : Day F G X} → from (to u) Day≈ u
    from-to {u = u@(day A B op (c , f) (d , g))} = ClEq.return (DayM.link f g (λ _ → ≡.refl))

    inverseˡ : ∀ {X} {x : H X} {y : Day F G X} → y Day≈ from x → to y ≈ x
    inverseˡ {x = x} {y = y} eq = trans (to-cong eq) to-from

    inverseʳ : ∀ {X} {x : Day F G X} {y : H X} → y ≈ to x → from y Day≈ x
    inverseʳ {x = x} {y = y} eq = trans (from-cong eq) from-to

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