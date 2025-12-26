{-# OPTIONS --without-K --safe #-}

-- A Comonad is a comonoid with respect to composition
-- of containers.
module Container.Coalgebra.Comonad where

open import Level

open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Data.Container.Core

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Compose as Compose
  using (Id; Comp; map₁; map₂)

private
  variable
    s p : Level

module _ {C : Container s p} where
  -- Less polymorphic operations
  unitLeft : Comp Id C ⇒ C
  unitLeft = Compose.unitLeft

  ununitLeft : C ⇒ Comp Id C
  ununitLeft = Compose.ununitLeft

  unitRight : Comp C Id ⇒ C
  unitRight = Compose.unitRight

  ununitRight : C ⇒ Comp C Id
  ununitRight = Compose.ununitRight

  assocʳ : Comp (Comp C C) C ⇒ Comp C (Comp C C)
  assocʳ = Compose.assocʳ

record RawComonad {s p} (C : Container s p) : Set (s ⊔ p) where
  field
    extract   : C ⇒ Id
    duplicate : C ⇒ Comp C C

record IsComonad {s p} (C : Container s p) (raw : RawComonad C) : Set (s ⊔ p) where
  open RawComonad raw

  field
    left-unit : unitLeft ∘ map₁ extract ∘ duplicate ≈ id C
    right-unit : unitRight ∘ map₂ extract ∘ duplicate ≈ id C
    assoc : assocʳ ∘ map₁ duplicate ∘ duplicate ≈ map₂ duplicate ∘ duplicate

record Comonad {s p} (C : Container s p) : Set (s ⊔ p) where
  field
    rawComonad : RawComonad C
    isComonad : IsComonad C rawComonad
  
  open RawComonad rawComonad public
  open IsComonad isComonad public

record IsComonadMorphism {s p} {C D : Container s p}
  (rawC : RawComonad C)
  (rawD : RawComonad D)
  (τ : C ⇒ D)
   : Set (s ⊔ p) where
  
  module WC = RawComonad rawC
  module WD = RawComonad rawD

  field
    preserve-extract : WC.extract ≈ WD.extract ∘ τ
    preserve-duplicate : map₁ τ ∘ map₂ τ ∘ WC.duplicate ≈ WD.duplicate ∘ τ

open import Container.Lax
open import Container.Combinator.Compose.Lax

module _ {s p} {C D : Container s p}
  (iso : C ⇔ D) where

  open _⇔_ iso
  open IsEquivalence {{...}}
  
  transferRawComonad : RawComonad C → RawComonad D
  transferRawComonad rawC = record {
      extract = RawComonad.extract rawC ∘ from ;
      duplicate = map₁ to ∘ map₂ to ∘ RawComonad.duplicate rawC ∘ from
    }
