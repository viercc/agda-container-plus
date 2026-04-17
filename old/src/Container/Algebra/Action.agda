{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Action where

open import Level

open import Function using (_∘_; _∘′_; id; _$_; const)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_; _≗_)

open import Data.Container.Core
open import Container.Morphism.Equality

open import Algebra using
  (Op₂; RawMonoid; IsMagma; IsSemigroup; IsMonoid; Monoid)

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

anythingIsMagma : ∀ {s} {S : Set s} {_·_ : Op₂ S}
  → IsMagma _≡_ _·_
anythingIsMagma = record {
    isEquivalence = ≡.isEquivalence;
    ∙-cong = ≡.cong₂ _
  }

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
    assoc : (x y z : S) → (x · y) · z ≡ x · (y · z)
    identityˡ : (x : S) → ε · x ≡ x
    identityʳ : (x : S) → x · ε ≡ x

    ϕleft-id : (x : S) → ϕleft ≗ [ identityʳ x ]
    ϕright-id : (x : S) → ϕright ≗ [ identityˡ x ]
    ϕleft-homo : (x y z : S)
      → ϕleft ∘ ϕleft ≗ ϕleft ∘ [ assoc x y z ]
    ϕright-homo : (x y z : S)
      → ϕright ≗ ϕright ∘ ϕright ∘ [ assoc x y z ]
    ϕinterchange : (x y z : S)
      → ϕright ∘ ϕleft ≗ ϕleft ∘ ϕright ∘ [ assoc x y z ]
  
  instance
    isMagma : IsMagma _≡_ _·_
    isMagma = anythingIsMagma

    isSemigroup : IsSemigroup _≡_ _·_
    isSemigroup = record {
        isMagma = isMagma;
        assoc = assoc
      }
    isMonoid : IsMonoid _≡_ _·_ ε
    isMonoid = record {
        isSemigroup = isSemigroup;
        identity = identityˡ , identityʳ
      }

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

module _ {s p} {Con : Container s p} where
  open Container Con renaming (Shape to S; Position to P)
  import Data.Container.Morphism as CM
  open import Container.Combinator.Tensor
  import Container.Algebra.TensorMonoid as ⊗

  module _ (raw : RawAction Con) where
    open RawAction raw
    private
      module impl where
        unit : Id ⇒ Con
        unit = const ε ▷ const tt

        mult : Con ⊗ Con ⇒ Con
        mult .shape (x , y) = x · y
        mult .position {s = x , y} p = ϕleft p , ϕright p

    packRaw : ⊗.RawMonoid Con
    packRaw = record { impl }
  
  module _ {raw : RawAction Con} (law : IsAction Con raw) where
    open RawAction raw
    open IsAction law renaming
      (identityˡ to S-identity-l;
      identityʳ to S-identity-r;
      assoc to S-assoc)

    raw' : ⊗.RawMonoid Con
    raw' = packRaw raw
    
    open ⊗.RawMonoid raw'

    private
      module impl where
        left-unit : mult CM.∘ map₁ unit ≈ unitLeft
        left-unit = mk≈
          (λ (_ , x) → S-identity-l x)
          (λ (_ , x) p → ≡.cong (tt ,_) (ϕright-id x p))
        
        right-unit : mult CM.∘ map₂ unit ≈ unitRight
        right-unit = mk≈
          (λ (x , _) → S-identity-r x)
          (λ (x , _) p → ≡.cong (_, tt) (ϕleft-id x p))
        
        assoc : mult CM.∘ map₁ mult ≈ mult CM.∘ map₂ mult CM.∘ assocʳ
        assoc = mk≈
          (λ ((x , y) , z) → S-assoc x y z)
          (λ ((x , y) , z) → eqP x y z)
          where
            eqP : ∀ (x y z : S) (p : P ((x · y) · z)) → _
            eqP x y z p =
              let eq1 = ϕleft-homo x y z p
                  eq2 = ϕinterchange x y z p
                  eq3 = ϕright-homo x y z p
              in ≡.cong₂ _,_ (≡.cong₂ _,_ eq1 eq2) eq3 
    
    packLaw : ⊗.IsMonoid Con raw'
    packLaw = record { impl }
  
  module _ (act : Action Con) where
    open Action act
    pack : ⊗.Monoid Con
    pack = record {
        rawMonoid = packRaw rawAction;
        isMonoid = packLaw isAction
      }

  module _ (raw : ⊗.RawMonoid Con) where
    open ⊗.RawMonoid raw
    
    unpackRaw : RawAction Con
    unpackRaw = record {rawImpl}
      where
        module rawImpl where
          ε : S
          ε = unit .shape tt

          _·_ : S → S → S
          _·_ x y = mult .shape (x , y)

          ϕleft : {x y : S} → P (x · y) → P x
          ϕleft p = mult .position p .proj₁

          ϕright : {x y : S} → P (x · y) → P y
          ϕright p = mult .position p .proj₂

  module _ {raw : ⊗.RawMonoid Con} (law : ⊗.IsMonoid Con raw) where
    open ⊗.RawMonoid raw
    open ⊗.IsMonoid law
      renaming (assoc to ⊗-assoc)

    private
      rawAction = unpackRaw raw
      open RawAction rawAction

      module lawImpl where
        assoc : (x y z : S) → (x · y) · z ≡ x · (y · z)
        assoc x y z = ⊗-assoc ._≈_.shape ((x , y) , z)

        identityˡ : (x : S) → ε · x ≡ x
        identityˡ x = left-unit ._≈_.shape (tt , x)

        identityʳ : (x : S) → x · ε ≡ x
        identityʳ x = right-unit ._≈_.shape (x , tt)

        open import Data.Product.Properties
          using ()
          renaming (,-injectiveˡ to injective-l; ,-injectiveʳ to injective-r)
        
        ϕleft-id : (x : S) → ϕleft ≗ ≡.subst P (identityʳ x)
        ϕleft-id x p = injective-l (right-unit ._≈_.position (x , tt) p)
        
        ϕright-id : (x : S) → ϕright ≗ ≡.subst P (identityˡ x)
        ϕright-id x p = injective-r (left-unit ._≈_.position (tt , x) p)

        ϕleft-homo : (x y z : S) → ϕleft ∘ ϕleft ≗ ϕleft ∘ ≡.subst P (assoc x y z)
        ϕleft-homo x y z p = injective-l (injective-l (⊗-assoc ._≈_.position _ p))

        ϕinterchange : (x y z : S) → ϕright ∘ ϕleft ≗ ϕleft ∘ ϕright ∘ ≡.subst P (assoc x y z)
        ϕinterchange x y z p = injective-r (injective-l (⊗-assoc ._≈_.position _ p))

        ϕright-homo : (x y z : S) → ϕright ≗ ϕright ∘ ϕright ∘ ≡.subst P (assoc x y z)
        ϕright-homo x y z p = injective-r (⊗-assoc ._≈_.position _ p)

    unpackLaw : IsAction Con rawAction
    unpackLaw = record {lawImpl}

  module _ (MC : ⊗.Monoid Con) where
    open ⊗.Monoid MC
    unpack : Action Con
    unpack = record {
        rawAction = unpackRaw rawMonoid;
        isAction = unpackLaw isMonoid
      } 