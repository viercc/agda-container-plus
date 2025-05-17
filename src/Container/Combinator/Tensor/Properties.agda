{-# OPTIONS --without-K --safe #-}

-- Properties of container tensor product _⊗_.
-- Especially, _⊗_ is Monoidal. All equalities hold definitionally.
-- (hence every proof is done by `refl`)
module Container.Combinator.Tensor.Properties where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

open import Data.Container.Core

open import Container.Morphism.Equality using (_≈_; mk≈)
open import Container.Morphism.Iso using (_⇔_; mk⇔)

open import Container.Combinator.Monoidal
open import Container.Combinator.Tensor

private
  variable
    c c' d d' e e' f f' : Level

open IsEquivalence {{...}}

module _ {c c' : Level} where
  functorial₁ : {D : Container d d'} → Functorial (_⊗ D) map₁
  functorial₁ {D = D} = record {
      map-id = refl;
      map-∘ = λ _ _ → refl
    }

  functorial₂ : {C : Container c c'} → Functorial (C ⊗_) map₂
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

module _ {c c'}
  {C : Container c c'}
  {D : Container c c'}
  {E : Container c c'} where
  assoc⇔ : (C ⊗ D) ⊗ E ⇔ C ⊗ (D ⊗ E)
  assoc⇔ = mk⇔ assocʳ assocˡ refl refl

semigroupal : {c : Level} → Semigroupal {c = c} {c' = c} _⊗_ map₁ map₂ assoc⇔
semigroupal {c} = record {
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