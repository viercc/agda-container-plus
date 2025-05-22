{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Action where

open import Level

open import Function using (_∘_; _∘′_; id; _$_; const)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; _≗_)

open import Data.Container.Core

open import Algebra using (Op₂; RawMonoid; IsMonoid; Monoid)

private
  variable
    s p e : Level

instance
  ≗-isEquivalence : ∀ {x y} {X : Set x} {Y : Set y}
    → IsEquivalence (_≗_ {A = X} {B = Y})
  ≗-isEquivalence = record
    { refl = λ _ → ≡.refl;
      sym = λ x≗y p → ≡.sym (x≗y p);
      trans = λ x≗y y≗z p → ≡.trans (x≗y p) (y≗z p)
    }

≗-setoid : ∀ {x y} (X : Set x) (Y : Set y) → Setoid (x ⊔ y) (x ⊔ y)
≗-setoid X Y = record { isEquivalence = ≗-isEquivalence {X = X} {Y = Y} }

module ContainerUtil (Con : Container s p) where
  open Container Con renaming (Shape to S; Position to P) public
  
  [_] : {x y : S} → x ≡ y → P x → P y
  [_] = ≡.subst P

  [_]' : {x y : S} → x ≡ y → P y → P x
  [_]' eq = ≡.subst P (≡.sym eq)

  infixr 8 _⨾_
  _⨾_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _⨾_ = ≡.trans

  []-trans : {x y z : S} {eq1 : x ≡ y} {eq2 : y ≡ z} →
    [ eq2 ] ∘′ [ eq1 ] ≗ [ eq1 ⨾ eq2 ]
  []-trans {eq1 = eq1} _ = ≡.subst-subst {P = P} eq1

  []-cancel : {x y : S} (eq : x ≡ y) →
    [ eq ] ∘′ [ eq ]' ≗ id
  []-cancel eq _ = ≡.subst-subst-sym eq

  []'-cancel : {x y : S} (eq : x ≡ y) →
    [ eq ]' ∘′ [ eq ] ≗ id
  []'-cancel eq _ = ≡.subst-sym-subst eq

-- Action of Con (Shape acting on Position): the data to define Applicative on ⟦ Con ⟧
record RawAction (Con : Container s p) : Set (s ⊔ p) where
  infixl 7 _·_

  open ContainerUtil Con using (S; P)

  field 
    _·_ : Op₂ S
    ε : S
    ϕleft : {x y : S} → P (x · y) → P x
    ϕright : {x y : S} → P (x · y) → P y
  
  ϕmid : {x y z : S} → P ((x · y) · z) → P y
  ϕmid = ϕright ∘ ϕleft

  instance
    rawMonoid : RawMonoid s s
    rawMonoid = record { Carrier = S; _≈_ = _≡_; _∙_ = _·_; ε = ε }

-- Laws on Action Con
record IsAction (Con : Container s p) (raw : RawAction Con) : Set (s ⊔ p) where
  open RawAction raw
  
  open ContainerUtil Con

  field
    instance
      isMonoid : IsMonoid _≡_ _·_ ε
  
  open IsMonoid isMonoid using (assoc; identityˡ; identityʳ) public
  
  field
    ϕleft-id : (x : S) → ϕleft ≗ [ identityʳ x ]
    
    ϕright-id : (x : S) → ϕright ≗ [ identityˡ x ]
    
    ϕleft-homo : (x y z : S)
      → ϕleft ∘ ϕleft ≗ ϕleft ∘ [ assoc x y z ]
    
    ϕright-homo : (x y z : S)
      → ϕright ≗ ϕright ∘ ϕright ∘ [ assoc x y z ]
    
    ϕinterchange : (x y z : S)
      → ϕright ∘ ϕleft ≗ ϕleft ∘ ϕright ∘ [ assoc x y z ]

record Action (Con : Container s p) : Set (s ⊔ p) where
  field
    instance
      rawAction : RawAction Con
      isAction : IsAction Con rawAction
  
  open RawAction rawAction public
  open IsAction isAction public

module Action-properties {Con : Container s p} (action : Action Con) where
  open ContainerUtil Con
  open Action action

  -- utils
  ϕleft-≡-natural : ∀ {x x' y y' : S}
    → (eq1 : x ≡ x') (eq2 : y ≡ y')
    → [ eq1 ] ∘′ ϕleft ≗ ϕleft ∘′ [ ≡.cong₂ _·_ eq1 eq2 ]
  ϕleft-≡-natural ≡.refl ≡.refl _ = ≡.refl

  indir-identityʳ : ∀ (x : S) {y : S} (eq : y ≡ ε)
    → x · y ≡ x
  indir-identityʳ x eq = ≡.cong (x ·_) eq ⨾ identityʳ x

  ϕleft-id-with : ∀ {x : S} {y : S} (eq : y ≡ ε)
    → ϕleft ≗ [ ≡.cong (x ·_) eq ⨾ identityʳ x ]
  ϕleft-id-with ≡.refl = ϕleft-id _

  ϕright-≡-natural : ∀ {x x' y y' : S}
    → (eq1 : x ≡ x') (eq2 : y ≡ y')
    → [ eq2 ] ∘′ ϕright ≗ ϕright ∘′ [ ≡.cong₂ _·_ eq1 eq2 ]
  ϕright-≡-natural ≡.refl ≡.refl _ = ≡.refl

  ϕright-id-with : ∀ {x : S} {y : S} (eq : x ≡ ε)
    → ϕright ≗ [ ≡.cong (_· y) eq ⨾ identityˡ y ]
  ϕright-id-with ≡.refl = ϕright-id _

  ϕmid-≡-natural : ∀ {x x' y y' z z' : S}
    → (eq1 : x ≡ x') (eq2 : y ≡ y') (eq3 : z ≡ z')
    → [ eq2 ] ∘′ ϕmid ≗ ϕmid ∘′ [ ≡.cong₂ _·_ (≡.cong₂ _·_ eq1 eq2) eq3 ]
  ϕmid-≡-natural ≡.refl ≡.refl ≡.refl _ = ≡.refl

  identity-mid : (x : S) → (ε · x · ε) ≡ x
  identity-mid x = identityʳ _ ⨾ identityˡ x

  ϕmid-id : (x : S) → ϕmid ≗ [ identity-mid x ]
  ϕmid-id x p = begin
      ϕmid p
    ≡⟨⟩
      ϕright (ϕleft p)
    ≡⟨ ϕright-id x (ϕleft p) ⟩
      [ identityˡ x ] (ϕleft p)
    ≡⟨ ≡.cong [ _ ] (ϕleft-id (ε · x) p) ⟩
      [ identityˡ x ] ([ identityʳ (ε · x) ] p)
    ≡⟨ ≡.subst-subst (identityʳ (ε · x)) ⟩
      [ identity-mid x ] p
    ∎
    where open ≡.≡-Reasoning
  
  ϕmid-id-with : ∀ {x y z : S} (eq1 : x ≡ ε) (eq3 : z ≡ ε)
    → ϕmid ≗ [ ≡.cong₂ _·_ (≡.cong (_· y) eq1) eq3 ⨾ identity-mid y ]
  ϕmid-id-with {y = y} ≡.refl ≡.refl = ϕmid-id y

  assoc-mid : (x' x y z z' : S) → x' · (x · y · z) · z' ≡ (x' · x) · y · (z · z')
  assoc-mid x' x y z z' =
      ≡.cong₂ _·_ (≡.sym (assoc x' (x · y) z)) ≡.refl ⨾
      assoc (x' · (x · y)) z z' ⨾
      ≡.cong₂ _·_ (≡.sym (assoc x' x y)) ≡.refl
  
  ϕright-homo⁻¹ : (x y z : S) →
    ϕright ∘ ϕright ≗ ϕright ∘ [ assoc x y z ]'
  ϕright-homo⁻¹ x y z p =
    begin
      (ϕright ∘ ϕright) p
    ≡⟨ ≡.cong (ϕright ∘ ϕright) ([]-cancel (assoc x y z) p) ⟨
      (ϕright ∘ ϕright) (([ assoc x y z ] ∘ [ assoc x y z ]') p)
    ≡⟨ ϕright-homo x y z ([ assoc x y z ]' p) ⟨
      ϕright ([ assoc x y z ]' p)
    ∎
    where open ≡.≡-Reasoning
  
  ϕinterchange⁻¹ : (x y z : S) →
    ϕleft ∘ ϕright ≗ ϕright ∘ ϕleft ∘ [ assoc x y z ]'
  ϕinterchange⁻¹ x y z p =
    begin
      (ϕleft ∘ ϕright) p
    ≡⟨ ≡.cong (ϕleft ∘ ϕright) ([]-cancel (assoc x y z) p) ⟨
      (ϕleft ∘ ϕright) (([ assoc x y z ] ∘ [ assoc x y z ]') p)
    ≡⟨ ϕinterchange x y z ([ assoc x y z ]' p) ⟨
      ϕright (ϕleft ([ assoc x y z ]' p))
    ∎
    where open ≡.≡-Reasoning

  ϕmid-mid : (x' x y z z' : S) → ϕmid ∘ ϕmid ≗ ϕmid ∘ [ assoc-mid x' x y z z' ]
  ϕmid-mid x' x y z z' p =
    -- p : P (x' · (x · y · z) · z')
    begin
      (ϕmid ∘ ϕmid) p
    ≡⟨⟩
      (ϕright ∘ ϕleft ∘ ϕright ∘ ϕleft) p
    ≡⟨ ≡.cong ϕright (ϕinterchange⁻¹ x' (x · y) z (ϕleft p)) ⟩
      (ϕright ∘ ϕright ∘ ϕleft ∘ [ eq1 ]' ∘ ϕleft) p
    ≡⟨ ≡.cong (ϕright ∘ ϕright ∘ ϕleft) (ϕleft-≡-natural (≡.sym eq1) ≡.refl _) ⟩
      (ϕright ∘ ϕright ∘ ϕleft ∘ ϕleft ∘ [ eq1' ] ) p
    ≡⟨ ≡.cong (ϕright ∘ ϕright) (ϕleft-homo (x' · (x · y)) z z' _) ⟩
      (ϕright ∘ ϕright ∘ ϕleft ∘ [ eq2 ] ∘ [ eq1' ] ) p
    ≡⟨ ≡.cong (ϕright ∘ ϕright ∘ ϕleft) (≡.subst-subst eq1') ⟩
      (ϕright ∘ ϕright ∘ ϕleft ∘ [ eq1' ⨾ eq2 ] ) p
    ≡⟨ ϕright-homo⁻¹ x' x y _ ⟩
      (ϕright ∘ [ eq3 ]' ∘ ϕleft ∘ [ eq1' ⨾ eq2 ] ) p
    ≡⟨ ≡.cong ϕright (ϕleft-≡-natural (≡.sym eq3) ≡.refl _) ⟩
      (ϕright ∘ ϕleft ∘ [ eq3' ] ∘ [ eq1' ⨾ eq2 ] ) p
    ≡⟨ ≡.cong (ϕright ∘ ϕleft) (≡.subst-subst (eq1' ⨾ eq2)) ⟩
      (ϕright ∘ ϕleft ∘ [ (eq1' ⨾ eq2) ⨾ eq3' ] ) p
    ≡⟨ ≡.cong (λ eq → (ϕright ∘ ϕleft ∘ [ eq ]) p) (≡.trans-assoc eq1') ⟩
      (ϕright ∘ ϕleft ∘ [ eq1' ⨾ eq2 ⨾ eq3' ] ) p
    ≡⟨⟩
      (ϕright ∘ ϕleft ∘ [ assoc-mid x' x y z z' ]) p
    ∎
    where
      open ≡.≡-Reasoning
      eq1 = assoc x' (x · y) z

      eq1' : (x' · (x · y · z)) · z' ≡ ((x' · (x · y)) · z) · z'
      eq1' = ≡.cong₂ _·_ (≡.sym eq1) ≡.refl 

      eq2 : ((x' · (x · y)) · z) · z' ≡ (x' · (x · y)) · (z · z')
      eq2 = assoc (x' · (x · y)) z z'

      eq3 = assoc x' x y

      eq3' : (x' · (x · y)) · (z · z') ≡ ((x' · x) · y) · (z · z')
      eq3' = ≡.cong₂ _·_ (≡.sym eq3) ≡.refl

module _ {C D : Container s p} (actionC : Action C) (actionD : Action D) where
  private
    module AC = Action actionC 
    module AD = Action actionD
  
  open Container C renaming (Shape to C₀; Position to C₁)
  open Container D renaming (Shape to D₀; Position to D₁)
  open RawAction {{...}}

  record IsActionMorphism (α : C ⇒ D) : Set (s ⊔ p) where
    open _⇒_ α renaming (shape to f; position to f#)

    field
      -- f is monoid homomorphism
      f-ε : f ε ≡ ε
      f-· : ∀ (x y : C₀) → f x · f y ≡ f (x · y)

      -- preservation of ϕleft,ϕright
      f#-ϕleft : ∀ (x y : C₀) (p : D₁ (f x · f y))
        → f# (ϕleft p) ≡ ϕleft (f# (≡.subst D₁ (f-· x y) p))
      
      f#-ϕright : ∀ (x y : C₀) (p : D₁ (f x · f y))
        → f# (ϕright p) ≡ ϕright (f# (≡.subst D₁ (f-· x y) p))