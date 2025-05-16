{-# OPTIONS --without-K --safe #-}

module Container.Combinator.Tensor where

open import Level using (Level; _⊔_; lower)
open import Data.Product as Product
  using (_×_; _,_; proj₁; proj₂; uncurry; curry)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Data.Sum.Base as Sum using ([_,_]′)
open import Data.Unit.Polymorphic.Base using (⊤)
import Function.Base as F

open import Data.Container.Core
import Data.Container.Combinator as CC

open import Effect.Functor.Day

module _ {s p} (C D : Container s p) where
  infixr 9 _⊗_

  _⊗_ : Container s p
  _⊗_ .Shape = Shape C × Shape D
  _⊗_ .Position = uncurry λ c d → Position C c × Position D d

  to-⊗ : ∀ {a} {A : Set a} → Day ⟦ C ⟧ ⟦ D ⟧ A → ⟦ _⊗_ ⟧ A
  to-⊗ (day _ (c , f) (d , g)) = ((c , d) , uncurry λ pc pd → f pc (g pd))

  from-⊗ : ∀ {A : Set p} → ⟦ _⊗_ ⟧ A → Day ⟦ C ⟧ ⟦ D ⟧ A
  from-⊗ ((c , d) , f) = day (Position D d) (c , λ pc pd → curry f pc pd) (d , F.id)

map₁ : ∀ {s p} {C₁ C₂ D : Container s p}
  → (C₁ ⇒ C₂) → C₁ ⊗ D ⇒ C₂ ⊗ D
map₁ α .shape (c , d) = (α .shape c , d)
map₁ α .position (pc , pd) = (α .position pc , pd)

map₂ : ∀ {s p} {C D₁ D₂ : Container s p}
  → (D₁ ⇒ D₂) → (C ⊗ D₁ ⇒ C ⊗ D₂)
map₂ β .shape (c , d) = (c , β .shape d)
map₂ β .position (pc , pd) = (pc , β .position pd)

module _ {s p} (C D E : Container s p) where
  assocʳ : (C ⊗ D) ⊗ E ⇒ C ⊗ (D ⊗ E)
  assocʳ = Product.assocʳ′ ▷ Product.assocˡ′

  assocˡ : C ⊗ (D ⊗ E) ⇒ (C ⊗ D) ⊗ E
  assocˡ = Product.assocˡ′ ▷ Product.assocʳ′

module _ {s p} (C : Container s p) where
  Id' : Container s p
  Id' = CC.id

  unitLeft : Id' ⊗ C ⇒ C
  unitLeft = proj₂ ▷ (tt ,_)

  ununitLeft : C ⇒ Id' ⊗ C
  ununitLeft = (tt ,_) ▷ proj₂

  unitRight : C ⊗ Id' ⇒ C
  unitRight = proj₁ ▷ (_, tt)

  ununitRight : C ⇒ C ⊗ Id'
  ununitRight = (_, tt) ▷ proj₁