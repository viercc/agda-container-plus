{-# OPTIONS --without-K --safe #-}

-- Properties of container compositions (Comp = CC._∘_).
-- Especially, Comp is Monoidal. All equalities hold definitionally.
-- (hence every proof is done by `refl`)
module Container.Combinator.Compose.Properties where

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

open import Container.Combinator.Compose

private
  variable
    c c' d d' e e' f f' : Level

open IsEquivalence {{...}}

open _⇔_
open ◇-util

-- Associativity

module _ {c c' d d' e e'}
  {C : Container c c'}
  {D : Container d d'}
  {E : Container e e'} where
  assoc⇔ : Comp (Comp C D) E ⇔ Comp C (Comp D E)
  assoc⇔ = mk⇔ assocʳ assocˡ refl refl

-- Units
module _ {c c'} {C : Container c c'} where
  unitLeft⇔ : Comp Id C ⇔ C
  unitLeft⇔ = record {
      to = unitLeft; from = ununitLeft;
      to-from = refl;
      from-to = refl
    }

  unitRight⇔ : Comp C Id ⇔ C
  unitRight⇔ = record {
      to = unitRight; from = ununitRight;
      to-from = refl;
      from-to = refl
    }
