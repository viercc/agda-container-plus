{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Action where

open import Level

open import Function using (_∘_; id; _$_; const)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using ()
    renaming (_≡_ to infix 3 _≡_)

open import Data.Container.Core

open import Algebra using (Op₂; RawMonoid; IsMonoid; Monoid)

private
  variable
    s p e : Level

-- Action of Con (Shape acting on Position): the data to define Applicative on ⟦ Con ⟧
record RawAction (Con : Container s p) : Set (s ⊔ p) where
  infixl 7 _·_

  S : Set s
  S = Shape Con

  P : S → Set p
  P = Position Con

  field 
    _·_ : Op₂ S
    ε : S
    ϕleft : {x y : S} → P (x · y) → P x
    ϕright : {x y : S} → P (x · y) → P y
  
  instance
    rawMonoid : RawMonoid s s
    rawMonoid = record { Carrier = S; _≈_ = _≡_; _∙_ = _·_; ε = ε }
  
  ϕmid : {x y z : S} → P (x · y · z) → P y
  ϕmid = ϕright ∘ ϕleft
  
  ϕmid' : {x y z : S} → P (x · (y · z)) → P y
  ϕmid' = ϕleft ∘ ϕright

-- Equivalence relation defined as Pointwise ≡
infixl 3 _≗_

_≗_ : ∀ {ℓ} {X Y : Set ℓ} → Rel (X → Y) ℓ
_≗_ f g = ∀ p → f p ≡ g p

≗-isEquivalence : ∀ {ℓ} {X Y : Set ℓ} → IsEquivalence (_≗_ {X = X} {Y = Y})
≗-isEquivalence = record
  { refl = λ _ → P.refl;
    sym = λ x≗y p → P.sym (x≗y p);
    trans = λ x≗y y≗z p → P.trans (x≗y p) (y≗z p)
  }

-- Laws on Action Con
record IsAction (Con : Container s p) (raw : RawAction Con) : Set (s ⊔ p) where
  open RawAction raw
  
  field
    instance
      isMonoid : IsMonoid _≡_ _·_ ε
  
  open IsMonoid isMonoid using (assoc; identityˡ; identityʳ) public
  
  lift≡ : {x y : S} → (x ≡ y) → P x → P y
  lift≡ = P.subst P

  lift≡' : {x y : S} → (x ≡ y) → P y → P x
  lift≡' eq = P.subst P (P.sym eq)
  
  field
    ϕleft-id : (x : S) → ϕleft ≗ lift≡ (identityʳ x)
    
    ϕright-id : (x : S) → ϕright ≗ lift≡ (identityˡ x)
    
    ϕleft-homo : (x y z : S)
      → ϕleft ∘ ϕleft ≗ ϕleft ∘ lift≡ (assoc x y z)
    
    ϕright-homo : (x y z : S)
      → ϕright ∘ ϕright ≗ ϕright ∘ lift≡' (assoc x y z)
    
    ϕinterchange : (x y z : S)
      → ϕright ∘ ϕleft ≗ ϕleft ∘ ϕright ∘ lift≡ (assoc x y z)

record Action (Con : Container s p) : Set (s ⊔ p) where
  field
    rawAction : RawAction Con
    isAction : IsAction Con rawAction
  
  open RawAction rawAction public
  open IsAction isAction public
