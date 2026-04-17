{-# OPTIONS --without-K --safe #-}

module Container.Combinator.Tensor where

open import Level using (Level; 0ℓ; _⊔_; Lift; lower)
open import Data.Product as Prod
  using (_×_; _,_; proj₁; proj₂; uncurry; curry)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Data.Sum.Base as Sum using ([_,_]′)
import Function.Base as F

open import Data.Container.Core
import Data.Container.Combinator as CC

open import Effect.Functor.Day

Id : Container 0ℓ 0ℓ
Id = CC.id

module _ {c c' d d'} (C : Container c c') (D : Container d d') where
  infixr 9 _⊗_

  _⊗_ : Container (c ⊔ d) (c' ⊔ d')
  _⊗_ .Shape = Shape C × Shape D
  _⊗_ .Position = uncurry λ c d → Position C c × Position D d

  to-⊗ : ∀ {x cx dx} {X : Set x} → Day {a = cx} {b = dx} ⟦ C ⟧ ⟦ D ⟧ X → ⟦ _⊗_ ⟧ X
  to-⊗ (day op (c , f) (d , g)) = ((c , d) , op F.∘′ Prod.map f g)

  from-⊗ : ∀ {x} {X : Set x} → ⟦ _⊗_ ⟧ X → Day ⟦ C ⟧ ⟦ D ⟧ X
  from-⊗ ((c , d) , f) =
    day f (c , F.id) (d , F.id)

module _ {c₁ c₁' c₂ c₂' d d'} {C₁ : Container c₁ c₁'} {C₂ : Container c₂ c₂'} {D : Container d d'} where

  map₁ : (C₁ ⇒ C₂) → C₁ ⊗ D ⇒ C₂ ⊗ D
  map₁ α .shape (c , d) = (α .shape c , d)
  map₁ α .position (pc , pd) = (α .position pc , pd)

map₂ : ∀ {c c' d₁ d₁' d₂ d₂'}
  {C : Container c c'} {D₁ : Container d₁ d₁'} {D₂ : Container d₂ d₂'}
  → (D₁ ⇒ D₂) → (C ⊗ D₁ ⇒ C ⊗ D₂)
map₂ β .shape (c , d) = (c , β .shape d)
map₂ β .position (pc , pd) = (pc , β .position pd)

module _ {c c' d d' e e'}
  {C : Container c c'} {D : Container d d'} {E : Container e e'} where
  assocʳ : (C ⊗ D) ⊗ E ⇒ C ⊗ (D ⊗ E)
  assocʳ = Prod.assocʳ′ ▷ Prod.assocˡ′

  assocˡ : C ⊗ (D ⊗ E) ⇒ (C ⊗ D) ⊗ E
  assocˡ = Prod.assocˡ′ ▷ Prod.assocʳ′


module _ {c c'} {C : Container c c'} where
  unitLeft : Id ⊗ C ⇒ C
  unitLeft = proj₂ ▷ (tt ,_)

  ununitLeft : C ⇒ Id ⊗ C
  ununitLeft = (tt ,_) ▷ proj₂

  unitRight : C ⊗ Id ⇒ C
  unitRight = proj₁ ▷ (_, tt)

  ununitRight : C ⇒ C ⊗ Id
  ununitRight = (_, tt) ▷ proj₁

module _ {c c' d d'} {C : Container c c'} {D : Container d d'} where
  swap : C ⊗ D ⇒ D ⊗ C
  swap = Prod.swap ▷ Prod.swap