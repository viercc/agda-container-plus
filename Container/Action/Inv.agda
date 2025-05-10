{-# OPTIONS --safe #-}

module Container.Action.Inv where

open import Level

open import Function using (_∘_; id; _$_; const)

open Function using (Inverseᵇ; Inverseˡ; Inverseʳ)

import Data.Product as Prod

open import Relation.Binary using (Rel; Setoid; IsEquivalence; _⇒_)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using ()
    renaming (_≡_ to infix 3 _≡_)

open import Relation.Binary.PropositionalEquality.WithK
  using (≡-irrelevant)

open import Data.Container.Core
import Data.Container.Properties as ContProp
open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)
import Data.Container.Relation.Binary.Equality.Setoid as CSetoid

open import Algebra using (Op₁; Op₂; RawMonoid; IsMonoid; Monoid; RawGroup; IsGroup; Group)

open import Container.Action

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
    → P.subst P eq x ≡ x
  subst-elim eq P x = P.cong (λ eq' → P.subst P eq' x) (≡-irrelevant eq P.refl)

  -- AxiomK
  ϕleft-≡-natural : ∀ {x y : S}
    → (x≡y : x ≡ y) → (z : S)
    → (lift≡ x≡y ∘ ϕleft x z) ≗ (ϕleft y z ∘ lift≡ (P.cong (_· z) x≡y))
  ϕleft-≡-natural P.refl _ p = P.refl
  
  -- AxiomK
  ϕleft-id' : ∀ (x : S) {y : S} (y≡ε : y ≡ ε)
    → ϕleft x y ≗ lift≡ (P.trans (P.cong (x ·_) y≡ε) (identityʳ x))
  ϕleft-id' x P.refl = ϕleft-id x

module _ {Con : Container s p} (actionInv : ActionInv Con) where
  open ActionInv actionInv
  open WithK actionInv
  
  module _ (x y : S) where
    y' : S
    y' = y ⁻¹
    
    xyy⁻¹≡x : (x · y) · y' ≡ x
    xyy⁻¹≡x =
      let open P.≡-Reasoning in
      begin
        (x · y) · y'
      ≡⟨ assoc _ _ _ ⟩
        x · (y · y')
      ≡⟨ P.cong (x ·_) (inverseʳ y)⟩
        x · ε
      ≡⟨ identityʳ x ⟩
        x
      ∎
    
    ϕx→xy : P x → P (x · y)
    ϕx→xy = ϕleft (x · y) y' ∘ lift≡' xyy⁻¹≡x
    
    ϕxy→x : P (x · y) → P x
    ϕxy→x = ϕleft x y
    
    ϕleft-inverse-l : Inverseˡ _≡_ _≡_ ϕxy→x ϕx→xy
    ϕleft-inverse-l {p} {q} P.refl =
      begin
        ϕxy→x (ϕx→xy p)
      ≡⟨⟩
        ϕleft x y (ϕleft (x · y) y' (lift≡ x≡xyy⁻¹ p))
      ≡⟨ ϕleft-homo x y y' _ ⟩
        ϕleft x (y · y') (lift≡ (assoc x y y') (lift≡ x≡xyy⁻¹ p))
      ≡⟨ P.cong (ϕleft _ _) (P.subst-subst {P = P} x≡xyy⁻¹) ⟩
        ϕleft x (y · y') (lift≡ x≡x·yy⁻¹ p)
      ≡⟨ ϕleft-id' x (inverseʳ y) _ ⟩
        lift≡ x·yy⁻¹≡x (lift≡ x≡x·yy⁻¹ p)
      ≡⟨ P.subst-subst {P = P} x≡x·yy⁻¹ ⟩
        lift≡ x≡x p
      ≡⟨ subst-elim x≡x P p ⟩
        p
      ∎
      where
        open P.≡-Reasoning { A = P x }
        x≡xyy⁻¹ = P.sym xyy⁻¹≡x
        x≡x·yy⁻¹ = P.trans x≡xyy⁻¹ (assoc x y y')
        x·yy⁻¹≡x = P.trans (P.cong (x ·_) (inverseʳ y)) (identityʳ x)
        x≡x = P.trans x≡x·yy⁻¹ x·yy⁻¹≡x
    
    ϕleft-inverse-r : Inverseʳ _≡_ _≡_ ϕxy→x ϕx→xy
    ϕleft-inverse-r {p} {q} P.refl =
      begin
        ϕx→xy (ϕxy→x p)
      ≡⟨⟩
        ϕleft (x · y) y' (lift≡ x≡xyy⁻¹ (ϕleft x y p))
      ≡⟨ P.cong (ϕleft _ _) (ϕleft-≡-natural x≡xyy⁻¹ y p) ⟩
        ϕleft (x · y) y' (ϕleft ((x · y) · y') y (lift≡ xy≡xyy⁻¹y p))
      ≡⟨ ϕleft-homo (x · y) y' y _ ⟩
        ϕleft (x · y) (y' · y) (lift≡ (assoc _ _ _) (lift≡ xy≡xyy⁻¹y p))
      ≡⟨ P.cong (ϕleft _ _) (P.subst-subst {P = P} (P.cong (_· y) x≡xyy⁻¹)) ⟩
        ϕleft (x · y) (y' · y) (lift≡ xy≡xy·y⁻¹y p)
      ≡⟨ ϕleft-id' (x · y) (inverseˡ y) (lift≡ xy≡xy·y⁻¹y p) ⟩
        lift≡ xy·y⁻¹y≡xy (lift≡ xy≡xy·y⁻¹y p)
      ≡⟨ P.subst-subst {P = P} xy≡xy·y⁻¹y ⟩
        lift≡ xy≡xy p
      ≡⟨ subst-elim xy≡xy P p ⟩
        p
      ∎
      where
        open P.≡-Reasoning { A = P (x · y) }
        x≡xyy⁻¹ = P.sym xyy⁻¹≡x
        xy≡xyy⁻¹y = P.cong (_· y) x≡xyy⁻¹
        xy≡xy·y⁻¹y = P.trans xy≡xyy⁻¹y (assoc (x · y) y' y)
        xy·y⁻¹y≡xy = P.trans (P.cong ((x · y) ·_) (inverseˡ y)) (identityʳ (x · y))
        xy≡xy = P.trans xy≡xy·y⁻¹y xy·y⁻¹y≡xy
    
    ϕleft-inverse : Inverseᵇ _≡_ _≡_ ϕxy→x ϕx→xy
    ϕleft-inverse = Prod._,_ ϕleft-inverse-l ϕleft-inverse-r

  module _ (x y : S) where
    x' : S
    x' = x ⁻¹

    x⁻¹xy≡y : x' · (x · y) ≡ y
    x⁻¹xy≡y =
      let open P.≡-Reasoning in
      begin
        x' · (x · y)
      ≡˘⟨ assoc _ _ _ ⟩
        (x' · x) · y
      ≡⟨ P.cong (_· y) (inverseˡ x) ⟩
        ε · y
      ≡⟨ identityˡ y ⟩
        y
      ∎
