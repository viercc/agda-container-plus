{-# OPTIONS --safe #-}

module Container.Algebra.Action.Inv where

open import Level

open import Function using (_∘_; id; _$_; const)

open Function using (Inverseᵇ; Inverseˡ; Inverseʳ)

import Data.Product as Prod

open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_)

open import Relation.Binary.PropositionalEquality.WithK
  using (≡-irrelevant)

open import Data.Container.Core
import Data.Container.Properties as ContProp
open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)
import Data.Container.Relation.Binary.Equality.Setoid as CSetoid

open import Algebra using (Op₁; Op₂; RawMonoid; IsMonoid; Monoid; RawGroup; IsGroup; Group)

open import Container.Algebra.Action

-- Container action by group is group action, hence are permutations

private
  variable
    a b c s p e : Level

record RawActionInv (Con : Container s p) : Set (s ⊔ p) where
  field
    rawAction : RawAction Con
    _⁻¹ : Op₁ (Shape Con)
  
  open RawAction rawAction public

  instance
    rawGroup : RawGroup s s
    rawGroup = record { Carrier = S; _≈_ = _≡_; _∙_ = _·_; ε = ε; _⁻¹ = _⁻¹ }

record IsActionInv (Con : Container s p) (raw : RawActionInv Con) : Set (s ⊔ p) where
  open RawActionInv raw
  
  field
    instance
      isAction : IsAction Con rawAction
    instance
      isGroup : IsGroup _≡_ _·_ ε _⁻¹

  open IsAction isAction public
  open IsGroup isGroup using (inverseˡ; inverseʳ) public

record ActionInv (Con : Container s p) : Set (s ⊔ p) where
  field
    raw : RawActionInv Con
    isActionInv : IsActionInv Con raw
  
  open RawActionInv raw public
  open IsActionInv isActionInv public

module WithK {Con : Container s p} (actionInv : ActionInv Con) where
  open ActionInv actionInv
  
  -- *** Axiom K ***
  subst-elim : ∀ {i} {I : Set i} {i : I} (eq : i ≡ i) (P : I → Set p) (x : P i)
    → ≡.subst P eq x ≡ x
  subst-elim eq P x = ≡.cong (λ eq' → ≡.subst P eq' x) (≡-irrelevant eq ≡.refl)

  -- AxiomK
  ϕleft-≡-natural : ∀ {x y : S}
    → (x≡y : x ≡ y) → (z : S)
    → (lift≡ x≡y ∘ ϕleft) ≗ (ϕleft ∘ lift≡ (≡.cong (_· z) x≡y))
  ϕleft-≡-natural ≡.refl _ p = ≡.refl
  
  -- AxiomK
  ϕleft-id' : ∀ (x : S) {y : S} (y≡ε : y ≡ ε)
    → ϕleft ≗ lift≡ (≡.trans (≡.cong (x ·_) y≡ε) (identityʳ x))
  ϕleft-id' x ≡.refl = ϕleft-id x

module _ {Con : Container s p} (actionInv : ActionInv Con) where
  open ActionInv actionInv
  open WithK actionInv
  
  module _ (x y : S) where
    y' : S
    y' = y ⁻¹
    
    xyy⁻¹≡x : (x · y) · y' ≡ x
    xyy⁻¹≡x =
      let open ≡.≡-Reasoning in
      begin
        (x · y) · y'
      ≡⟨ assoc _ _ _ ⟩
        x · (y · y')
      ≡⟨ ≡.cong (x ·_) (inverseʳ y)⟩
        x · ε
      ≡⟨ identityʳ x ⟩
        x
      ∎
    
    ϕx→xy : P x → P (x · y)
    ϕx→xy = ϕleft ∘ lift≡' xyy⁻¹≡x
    
    ϕxy→x : P (x · y) → P x
    ϕxy→x = ϕleft
    
    ϕleft-inverse-l : Inverseˡ _≡_ _≡_ ϕxy→x ϕx→xy
    ϕleft-inverse-l {p} {q} ≡.refl =
      begin
        ϕxy→x (ϕx→xy p)
      ≡⟨⟩
        ϕleft (ϕleft (lift≡ x≡xyy⁻¹ p))
      ≡⟨ ϕleft-homo x y y' _ ⟩
        ϕleft (lift≡ (assoc x y y') (lift≡ x≡xyy⁻¹ p))
      ≡⟨ ≡.cong ϕleft (≡.subst-subst {P = P} x≡xyy⁻¹) ⟩
        ϕleft (lift≡ x≡x·yy⁻¹ p)
      ≡⟨ ϕleft-id' x (inverseʳ y) _ ⟩
        lift≡ x·yy⁻¹≡x (lift≡ x≡x·yy⁻¹ p)
      ≡⟨ ≡.subst-subst {P = P} x≡x·yy⁻¹ ⟩
        lift≡ x≡x p
      ≡⟨ subst-elim x≡x P p ⟩
        p
      ∎
      where
        open ≡.≡-Reasoning { A = P x }
        x≡xyy⁻¹ = ≡.sym xyy⁻¹≡x
        x≡x·yy⁻¹ = ≡.trans x≡xyy⁻¹ (assoc x y y')
        x·yy⁻¹≡x = ≡.trans (≡.cong (x ·_) (inverseʳ y)) (identityʳ x)
        x≡x = ≡.trans x≡x·yy⁻¹ x·yy⁻¹≡x
    
    ϕleft-inverse-r : Inverseʳ _≡_ _≡_ ϕxy→x ϕx→xy
    ϕleft-inverse-r {p} {q} ≡.refl =
      begin
        ϕx→xy (ϕxy→x p)
      ≡⟨⟩
        ϕleft (lift≡ x≡xyy⁻¹ (ϕleft p))
      ≡⟨ ≡.cong ϕleft (ϕleft-≡-natural x≡xyy⁻¹ y p) ⟩
        ϕleft (ϕleft (lift≡ xy≡xyy⁻¹y p))
      ≡⟨ ϕleft-homo (x · y) y' y _ ⟩
        ϕleft (lift≡ (assoc _ _ _) (lift≡ xy≡xyy⁻¹y p))
      ≡⟨ ≡.cong ϕleft (≡.subst-subst {P = P} (≡.cong (_· y) x≡xyy⁻¹)) ⟩
        ϕleft (lift≡ xy≡xy·y⁻¹y p)
      ≡⟨ ϕleft-id' (x · y) (inverseˡ y) (lift≡ xy≡xy·y⁻¹y p) ⟩
        lift≡ xy·y⁻¹y≡xy (lift≡ xy≡xy·y⁻¹y p)
      ≡⟨ ≡.subst-subst {P = P} xy≡xy·y⁻¹y ⟩
        lift≡ xy≡xy p
      ≡⟨ subst-elim xy≡xy P p ⟩
        p
      ∎
      where
        open ≡.≡-Reasoning { A = P (x · y) }
        x≡xyy⁻¹ = ≡.sym xyy⁻¹≡x
        xy≡xyy⁻¹y = ≡.cong (_· y) x≡xyy⁻¹
        xy≡xy·y⁻¹y = ≡.trans xy≡xyy⁻¹y (assoc (x · y) y' y)
        xy·y⁻¹y≡xy = ≡.trans (≡.cong ((x · y) ·_) (inverseˡ y)) (identityʳ (x · y))
        xy≡xy = ≡.trans xy≡xy·y⁻¹y xy·y⁻¹y≡xy
    
    ϕleft-inverse : Inverseᵇ _≡_ _≡_ ϕxy→x ϕx→xy
    ϕleft-inverse = Prod._,_ ϕleft-inverse-l ϕleft-inverse-r

  module _ (x y : S) where
    x' : S
    x' = x ⁻¹

    x⁻¹xy≡y : x' · (x · y) ≡ y
    x⁻¹xy≡y =
      let open ≡.≡-Reasoning in
      begin
        x' · (x · y)
      ≡˘⟨ assoc _ _ _ ⟩
        (x' · x) · y
      ≡⟨ ≡.cong (_· y) (inverseˡ x) ⟩
        ε · y
      ≡⟨ identityˡ y ⟩
        y
      ∎
