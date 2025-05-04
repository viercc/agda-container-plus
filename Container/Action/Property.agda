{-# OPTIONS --safe #-}

module Container.Action.Property where

open import Level

open import Function using (_∘_; id; _$_; const)

open Function using (Inverseᵇ; Inverseˡ; Inverseʳ)

import Data.Product as Prod

open import Relation.Binary using (Rel; Setoid; IsEquivalence; _⇒_)
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using ()
    renaming (_≡_ to infix 3 _≡_)

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
    s p e : Level

record RawActionInv (Con : Container s p) : Set (s ⊔ p) where
  field
    rawAction : RawAction Con
    _⁻¹ : Op₁ (Shape Con)

record IsActionInv (Con : Container s p) (raw : RawActionInv Con) : Set (s ⊔ p) where
  open RawActionInv raw public
  open RawAction rawAction

  field
    isAction : IsAction Con rawAction
    isGroup : IsGroup _≡_ _·_ ε _⁻¹

  open IsAction isAction public
  open IsGroup isGroup using (⁻¹-cong; inverseˡ; inverseʳ) public
  
  inverse-left-action : ∀(x y : S) → (x ⁻¹ · (x · y) ≡ y)
  inverse-left-action x y = begin
      x ⁻¹ · (x · y)
    ≡˘⟨ assoc _ _ _ ⟩
      (x ⁻¹ · x) · y
    ≡⟨ ·-cong (inverseˡ x) P.refl ⟩
      ε · y
    ≡⟨ identityˡ y ⟩
      y
    ∎
    where
      open P.≡-Reasoning { A = S }

  inverse-right-action : ∀(x y : S) → ((x · y) · y ⁻¹ ≡ x)
  inverse-right-action x y = begin
      (x · y) · y ⁻¹
    ≡⟨ assoc _ _ _ ⟩
      x · (y · y ⁻¹)
    ≡⟨ ·-cong P.refl (inverseʳ y)⟩
      x · ε
    ≡⟨ identityʳ x ⟩
      x
    ∎
    where
      open P.≡-Reasoning { A = S }
  
  ϕleft-inverse : ∀(x y : S)
    (let x≡xyy⁻¹ = P.sym (inverse-right-action x y))
    → Inverseᵇ _≡_ _≡_ (ϕleft x y) (ϕleft (x · y) (y ⁻¹) ∘ lift≡ x≡xyy⁻¹)
  ϕleft-inverse x y = Prod._,_ inv_l inv_r
    where
      open P.≡-Reasoning { A = P x }
      
      x≡xyy⁻¹ = P.sym (inverse-right-action x y)
      x≡x·yy⁻¹ = P.trans x≡xyy⁻¹ (assoc x y (y ⁻¹))
      x≡xε = P.trans x≡x·yy⁻¹ (P.cong (x ·_) (inverseʳ y))
      x≡x = P.trans x≡xε (identityʳ x)
      
      inv_l : Inverseˡ _≡_ _≡_ (ϕleft x y) (ϕleft (x · y) (y ⁻¹) ∘ lift≡ x≡xyy⁻¹)
      inv_l {p} {q} P.refl = begin
          ϕleft x y (ϕleft (x · y) (y ⁻¹) (lift≡ x≡xyy⁻¹ p))
        ≡⟨ ϕleft-homo x y (y ⁻¹) _ ⟩
          ϕleft x (y · y ⁻¹) (lift≡ (assoc x y (y ⁻¹)) (lift≡ x≡xyy⁻¹ p))
        ≡⟨ P.cong (ϕleft _ _) (P.subst-subst {P = P} x≡xyy⁻¹) ⟩
          ϕleft x (y · y ⁻¹) (lift≡ x≡x·yy⁻¹ p)
        ≡⟨ P.dcong₂ (ϕleft x) (inverseʳ y) P.refl ⟩
          ϕleft x ε (P.subst (λ z → P (x · z)) (inverseʳ y) (lift≡ x≡x·yy⁻¹ p))
        ≡⟨ P.cong (ϕleft x ε) (P.subst-∘ (inverseʳ y)) ⟩
          ϕleft x ε (P.subst P (P.cong (x ·_) (inverseʳ y))
            (lift≡ x≡x·yy⁻¹ p)
          )
        ≡⟨ P.cong (ϕleft x ε) (P.subst-subst x≡x·yy⁻¹) ⟩
          ϕleft x ε (lift≡ x≡xε p)
        ≡⟨ ϕleft-id x _ ⟩
          lift≡ (identityʳ x) (lift≡ x≡xε p)
        ≡⟨ P.subst-subst x≡xε ⟩
          lift≡ x≡x p
        ≡⟨ subst-elim x≡x P p ⟩
          p
        ∎
      
      inv_r : Inverseʳ _≡_ _≡_ (ϕleft x y) (ϕleft (x · y) (y ⁻¹) ∘ lift≡ x≡xyy⁻¹)
      inv_r {p} {q} P.refl = {! !}
  