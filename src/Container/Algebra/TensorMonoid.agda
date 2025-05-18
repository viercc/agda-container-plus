{-# OPTIONS --without-K --safe #-}

-- Monoid with respect to ⊗.
module Container.Algebra.TensorMonoid where

open import Level

import Function as F
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product as Prod
  using (Σ; _×_; _,_; proj₁; proj₂)
  renaming (_,′_ to pair)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)

open import Data.Container.Core

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality
open import Container.Morphism.Iso using (_⇔_)
open import Container.Combinator.Tensor as T
  using (Id; _⊗_; map₁; map₂)


module _ {s p} {C : Container s p} where
  -- Less polymorphic operations
  unitLeft : Id ⊗ C ⇒ C
  unitLeft = T.unitLeft

  unitRight : C ⊗ Id ⇒ C
  unitRight = T.unitRight

  assocʳ : (C ⊗ C) ⊗ C ⇒ C ⊗ (C ⊗ C)
  assocʳ = T.assocʳ

record RawMonoid {s p} (C : Container s p) : Set (s ⊔ p) where
  field
    unit : Id {s} {p} ⇒ C
    mult : C ⊗ C ⇒ C

record IsMonoid {s p} (C : Container s p) (raw : RawMonoid C) : Set (s ⊔ p) where
  open RawMonoid raw

  field
    left-unit : mult ∘ map₁ unit ≈ unitLeft
    right-unit : mult ∘ map₂ unit ≈ unitRight
    assoc : mult ∘ map₁ mult ≈ mult ∘ map₂ mult ∘ assocʳ

record Monoid {s p} (Con : Container s p) : Set (s ⊔ p) where
  field
    rawMonoid : RawMonoid Con
    isMonoid : IsMonoid Con rawMonoid
  
  open RawMonoid rawMonoid public
  open IsMonoid isMonoid public

-- TODO: TensorMonoid ↔ Action
--   (probably I should rename Action to TensorMonoid.Uustalu)

module ToAction {s p} (Con : Container s p) where
  open import Container.Algebra.Action
  open Container Con renaming (Shape to S; Position to P)

  module _ (raw : RawMonoid Con) where
    open RawMonoid raw

    private
      module rawImpl where
        ε : S
        ε = unit .shape tt

        _·_ : S → S → S
        _·_ x y = mult .shape (x , y)

        ϕleft : {x y : S} → P (x · y) → P x
        ϕleft p = mult .position p .proj₁

        ϕright : {x y : S} → P (x · y) → P y
        ϕright p = mult .position p .proj₂
    
    toRawAction : RawAction Con
    toRawAction = record {rawImpl}

  module _ (raw : RawMonoid Con) (law : IsMonoid Con raw) where
    open RawMonoid raw
    open IsMonoid law

    private
      rawAction = toRawAction raw
      open RawAction rawAction hiding (S; P)
      
      import Algebra.Structures
      open import Algebra.Structures.PatternSynonyms

      module lawImpl where
        isMonoid : Algebra.Structures.IsMonoid _≡_ _·_ ε
        isMonoid =
          mkIsMonoid ≡.isEquivalence (≡.cong₂ _·_)
            (λ x y z → assoc ._≈_.shape ((x , y) , z))
            (λ x → left-unit ._≈_.shape (tt , x))
            (λ x → right-unit ._≈_.shape (x , tt))

        module SM = Algebra.Structures.IsMonoid isMonoid
        
        open import Data.Product.Properties
          using ()
          renaming (,-injectiveˡ to injective-l; ,-injectiveʳ to injective-r)
        
        ϕleft-id : (x : S) → ϕleft ≗ ≡.subst P (SM.identityʳ x)
        ϕleft-id x p = injective-l (right-unit ._≈_.position (x , tt) p)
        
        ϕright-id : (x : S) → ϕright ≗ ≡.subst P (SM.identityˡ x)
        ϕright-id x p = injective-r (left-unit ._≈_.position (tt , x) p)

        ϕleft-homo : (x y z : S) → ϕleft F.∘ ϕleft ≗ ϕleft F.∘ ≡.subst P (SM.assoc x y z)
        ϕleft-homo x y z p = injective-l (injective-l (assoc ._≈_.position _ p))

        ϕinterchange : (x y z : S) → ϕright F.∘ ϕleft ≗ ϕleft F.∘ ϕright F.∘ ≡.subst P (SM.assoc x y z)
        ϕinterchange x y z p = injective-r (injective-l (assoc ._≈_.position _ p))

        ϕright-homo : (x y z : S) → ϕright ≗ ϕright F.∘ ϕright F.∘ ≡.subst P (SM.assoc x y z)
        ϕright-homo x y z p = injective-r (assoc ._≈_.position _ p)

    toIsAction : IsAction Con rawAction
    toIsAction = record {lawImpl}