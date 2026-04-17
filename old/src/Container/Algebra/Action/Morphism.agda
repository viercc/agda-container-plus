{-# OPTIONS --without-K --safe #-}

-- Action morphism
module Container.Algebra.Action.Morphism where

open import Level

import Function as F
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product as Prod
  using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties as ProdProp

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

open import Data.Container.Core

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Tensor as T
  using (Id; _⊗_; map₁; map₂)

open import Container.Algebra.TensorMonoid
import Container.Algebra.TensorMonoid.Morphism as ⊗
open import Container.Algebra.Action

private
  variable
    c c' d d' : Level

module _ {C : Container c c'} {D : Container d d'}
  {{AC : RawAction C}} {{AD : RawAction D}} where
  open Container C renaming (Shape to C₀; Position to C₁)
  open Container D renaming (Shape to D₀; Position to D₁)
  open RawAction {{...}}

  record IsMorphism (α : C ⇒ D) : Set (c ⊔ c' ⊔ d ⊔ d') where
    open _⇒_ α renaming (shape to f; position to f#)

    field
      -- f is monoid homomorphism
      f-ε : f ε ≡ ε
      f-· : ∀ (x y : C₀) → f (x · y) ≡ f x · f y

      -- preservation of ϕleft,ϕright
      f#-ϕleft : ∀ (x y : C₀) (p : D₁ (f (x · y)))
        → ϕleft (f# p) ≡ f# (ϕleft (≡.subst D₁ (f-· x y) p))
      
      f#-ϕright : ∀ (x y : C₀) (p : D₁ (f (x · y)))
        → ϕright (f# p) ≡ f# (ϕright (≡.subst D₁ (f-· x y) p))

module _ {C : Container c c'} {D : Container d d'} {{AC : RawAction C}} {{AD : RawAction D}} where
  open Container C renaming (Shape to C₀; Position to C₁)
  open Container D renaming (Shape to D₀; Position to D₁)
  
  private
    instance
      MC : RawMonoid C
      MC = packRaw AC

      MD : RawMonoid D
      MD = packRaw AD

  packMorphismLaw : ∀ {α : C ⇒ D} → IsMorphism α → ⊗.IsMorphism α
  packMorphismLaw {α = ff@(f ▷ f#)} law = record {impl}
    where
      open IsMorphism law
      open RawAction {{...}}
      open RawMonoid {{...}}
      module impl where
        preserve-unit : ff ∘ unit ≈ unit
        preserve-unit = mk≈ (λ _ → f-ε) (λ _ _ → ≡.refl)

        preserve-mult-pos :
          ∀ ((x , y) : C₀ × C₀) (p : D₁ (f (x · y)))
            (let p' = ≡.subst D₁ (f-· x y) p)
          → (ϕleft (f# p) , ϕright (f# p))
              ≡
            (f# (ϕleft p') , f# (ϕright p'))  
        preserve-mult-pos (x , y) p = ProdProp.×-≡,≡→≡ (f#-ϕleft x y p , f#-ϕright x y p)

        preserve-mult : ff ∘ mult ≈ mult ∘ map₁ ff ∘ map₂ ff
        preserve-mult = mk≈ (λ (x , y) → f-· x y) preserve-mult-pos

  unpackMorphismLaw : ∀ {α : C ⇒ D} → ⊗.IsMorphism α → IsMorphism α
  unpackMorphismLaw {α = ff@(f ▷ f#)} law = record {impl}
    where
      open ⊗.IsMorphism law
      open RawAction {{...}}
      open RawMonoid {{...}}

      module impl where
        f-ε : f ε ≡ ε
        f-ε = preserve-unit ._≈_.shape tt

        f-· : ∀ (x y : C₀) → f (x · y) ≡ f x · f y
        f-· x y = preserve-mult ._≈_.shape (x , y)

        f#-ϕ : ∀ (x y : C₀) (p : D₁ (f (x · y)))
            (let p' = ≡.subst D₁ (f-· x y) p)
          → (ϕleft (f# p) , ϕright (f# p))
              ≡
            (f# (ϕleft p') , f# (ϕright p'))
        f#-ϕ x y p = preserve-mult ._≈_.position (x , y) p

        f#-ϕleft : ∀ (x y : C₀) (p : D₁ (f (x · y)))
          → ϕleft (f# p) ≡ f# (ϕleft (≡.subst D₁ (f-· x y) p))
        f#-ϕleft x y p = ProdProp.,-injectiveˡ (f#-ϕ x y p)
        
        f#-ϕright : ∀ (x y : C₀) (p : D₁ (f (x · y)))
          → ϕright (f# p) ≡ f# (ϕright (≡.subst D₁ (f-· x y) p))
        f#-ϕright x y p = ProdProp.,-injectiveʳ (f#-ϕ x y p)

module _ {C : Container c c'} {D : Container d d'} {{AC : RawAction C}} {{AD : RawAction D}} where
  private
    instance
      MC : RawMonoid C
      MC = packRaw AC

      MD : RawMonoid D
      MD = packRaw AD

  IsIsomorphism : (iso : C ⇔ D) → Set _
  IsIsomorphism (record {to = f; from = g}) =
    IsMorphism f × IsMorphism g
  
  inverseIsMorphism :
      (iso : C ⇔ D)
    → IsMorphism (iso ._⇔_.to)
    → IsMorphism (iso ._⇔_.from)
  inverseIsMorphism iso
    = unpackMorphismLaw F.∘ ⊗.inverseIsMorphism iso F.∘ packMorphismLaw

module _ {C : Container c c'} {D : Container d d'} (iso : C ⇔ D) where
  transferRawAction : RawAction C → RawAction D
  transferRawAction = unpackRaw F.∘ ⊗.transferRawMonoid iso F.∘ packRaw

  module _ {{AC : RawAction C}} where
    private
      instance
        MC : RawMonoid C
        MC = packRaw AC

    to-morphism : IsMorphism {{AD = transferRawAction AC}} (iso ._⇔_.to)
    to-morphism = unpackMorphismLaw {{AD = transferRawAction AC}} (⊗.to-morphism iso)

    from-morphism : IsMorphism {{AC = transferRawAction AC}} (iso ._⇔_.from)
    from-morphism = unpackMorphismLaw {{AC = transferRawAction AC}} (⊗.from-morphism iso)

    isomorphism : IsIsomorphism {{AD = transferRawAction AC}} iso
    isomorphism = to-morphism , from-morphism
  
  transferIsAction :
      {raw : RawAction C}
    → IsAction C raw
    → IsAction D (transferRawAction raw)
  transferIsAction = unpackLaw F.∘ ⊗.transferIsMonoid iso F.∘ packLaw

  transfer : Action C → Action D
  transfer = unpack F.∘ ⊗.transfer iso F.∘ pack
