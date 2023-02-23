{-# OPTIONS --without-K --safe #-}

module Container.Action where

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
    ϕleft : (x y : S) → P (x · y) → P x
    ϕright : (x y : S) → P (x · y) → P y
  
  instance
    rawMonoid : RawMonoid s s
    rawMonoid = record { Carrier = S; _≈_ = _≡_; _∙_ = _·_; ε = ε }
  
  open RawMonoid rawMonoid using (_≉_; rawMagma) public
  
  ϕmid : (x y z : S) → P (x · y · z) → P y
  ϕmid x y z = ϕright x y ∘ ϕleft (x · y) z
  
  ϕmid' : (x y z : S) → P (x · (y · z)) → P y
  ϕmid' x y z = ϕleft y z ∘ ϕright x (y · z)

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

subst-inv : ∀ {I : Set s} {i j : I} (eq : i ≡ j) (P : I → Set p) (p : P i)
  → P.subst P (P.sym eq) (P.subst P eq p) ≡ p
subst-inv P.refl _ p = P.refl

-- Laws on Action Con
record IsAction (Con : Container s p) (raw : RawAction Con) : Set (s ⊔ p) where
  open RawAction raw
  
  field
    instance
      isMonoid : IsMonoid _≡_ _·_ ε
  
  open IsMonoid isMonoid renaming (∙-cong to ·-cong) public
  
  field
    ϕleft-id : (x : S) → ϕleft x ε ≗ P.subst P (identityʳ x)
    
    ϕright-id : (x : S) → ϕright ε x ≗ P.subst P (identityˡ x)
    
    ϕleft-homo : (x y z : S)
      → ϕleft x y ∘ ϕleft (x · y) z ≗ ϕleft x (y · z) ∘ P.subst P (assoc x y z)
    
    ϕright-homo : (x y z : S)
      → ϕright y z ∘ ϕright x (y · z) ≗ ϕright (x · y) z ∘ P.subst P (P.sym (assoc x y z))
    
    ϕinterchange : (x y z : S)
      → ϕmid x y z ≗ ϕmid' x y z ∘ P.subst P (assoc x y z)
  
  ϕright-homo' : (x y z : S)
    → ϕright (x · y) z ≗ ϕright y z ∘ ϕright x (y · z) ∘ P.subst P (assoc x y z)
  ϕright-homo' x y z p =
    P.sym $
    P.trans (ϕright-homo x y z (P.subst P eq p)) $
    P.cong (ϕright (x · y) z) (subst-inv eq P p)
    where
      eq = assoc x y z
