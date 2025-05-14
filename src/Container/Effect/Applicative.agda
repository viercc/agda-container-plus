{-# OPTIONS --without-K --safe #-}

module Container.Effect.Applicative where

open import Level

open import Function using (_∘_; _∘′_; id; _$_; const)

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product as Prod
  using (Σ; _×_; _,_; proj₁; proj₂)
  renaming (_,′_ to pair)

open import Data.Product.Properties
  using (,-injective)

open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)

open import Axiom.UniquenessOfIdentityProofs using (UIP)

open import Data.Container.Core
import Data.Container.Properties as ContProp
open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)
import Data.Container.Relation.Binary.Equality.Setoid as CSetoid

open import Algebra using (Op₂; RawMonoid; IsMonoid; Monoid)

open import Effect.Functor
open import Effect.Applicative
open import Effect.Functor.Law
open import Effect.Applicative.Law
open import Effect.Applicative.Properties

open import Container.Algebra.Action
open import Container.Effect.Functor

private
  variable
    s p : Level

-- Make RawApplicative out of RawAction
module _ {Con : Container s p} (raw : RawAction Con) where
  private
    open RawAction raw
    open Prod using (_,_)
    
    module applicativeImpl (e : Level) where
      variable
        A B C : Set e
      
      rawFunctor = makeRawFunctor Con e

      pure : A → ⟦ Con ⟧ A
      pure a = (ε , const a)

      _<*>_ : ⟦ Con ⟧ (A → B) → ⟦ Con ⟧ A → ⟦ Con ⟧ B
      _<*>_ (x , f) (y , g) = (x · y , λ (i : P (x · y)) → f (ϕleft i) (g (ϕright i)))

  makeRawApplicative : (e : Level) → RawApplicative {f = e} (⟦ Con ⟧)
  makeRawApplicative e = record {applicativeImpl e}

-- Make Applicative (with law) out of Action (with law)
module _ {Con : Container s p} (action : Action Con) where
  open Action action
  
  private
    ≡-cong₃ : ∀ {a e : Level} {X Y Z : Set a} {R : Set e}
      → (f : X → Y → Z → R)
      → {x1 x2 : X} → (x1 ≡ x2)
      → {y1 y2 : Y} → (y1 ≡ y2)
      → {z1 z2 : Z} → (z1 ≡ z2)
      → (f x1 y1 z1 ≡ f x2 y2 z2)
    ≡-cong₃ f ≡.refl ≡.refl ≡.refl = ≡.refl

    module _ (x y z : S) where
      ϕright-homo' : ϕright ∘ ϕright ∘ lift≡ (assoc x y z) ≗ ϕright
      ϕright-homo' p =
        begin
          ϕright (ϕright (lift≡ eq p))
        ≡⟨ ϕright-homo x y z (lift≡ eq p) ⟩
          ϕright (lift≡' eq (lift≡ eq p))
        ≡⟨ ≡.cong ϕright (≡.subst-sym-subst eq) ⟩
          ϕright p
        ∎
        where
          open ≡.≡-Reasoning
          eq = assoc x y z
    
    module isApplicativeImpl (e : Level) where
      variable
        A B C : Set e
      
      open RawApplicative (makeRawApplicative rawAction e)

      isFunctor = makeIsFunctor Con e
      open IsFunctor isFunctor
      
      F : Set e → Set (s ⊔ p ⊔ e)
      F = ⟦ Con ⟧
      
      <*>-cong : ∀ {u₁ u₂ : F (A → B)} {v₁ v₂ : F A}
        → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (u₁ <*> v₁ ≈ u₂ <*> v₂)
      <*>-cong {u₁ = x , _} {v₁ = y , _} (Pw ≡.refl f≗) (Pw ≡.refl g≗) = Pw ≡.refl fg≗
        where
          fg≗ = λ (p : P (x · y)) → ≡.cong₂ (_$_) (f≗ (ϕleft p)) (g≗ (ϕright p)) 

      ap-map : ∀ (f : A → B) (v : F A) → pure f <*> v ≈ f <$> v
      ap-map f (y , g) = Pw (identityˡ y) (λ p → ≡.cong (f ∘ g) (ϕright-id y p))

      homomorphism : ∀ (f : A → B) (x : A) → pure f <*> pure x ≈ pure (f x)
      homomorphism f x = Pw (identityˡ ε) (λ p → ≡.refl)

      interchange : ∀ (u : F (A → B)) (y : A) → u <*> pure y ≈ (λ f → f y) <$> u
      interchange (x , f) y = Pw (identityʳ x) (λ p → ≡.cong (λ q → f q y) (ϕleft-id x p))

      composition : ∀ (u : F (B → C)) (v : F (A → B)) (w : F A)
        → _∘′_ <$> u <*> v <*> w ≈ u <*> (v <*> w)
      composition (x , f) (y , g) (z , h) =
        Pw (assoc x y z) fgh-equality
        where          
          fgh-equality : _
          fgh-equality p =
            ≡-cong₃ (λ p₁ p₂ p₃ → f p₁ (g p₂ (h p₃)))
              (ϕleft-homo x y z p)
              (ϕinterchange x y z p)
              (≡.sym (ϕright-homo' x y z p))

  makeIsApplicative : (e : Level) → IsApplicative ⟦ Con ⟧ _≈_ (makeRawApplicative rawAction e)
  makeIsApplicative e = record{
      isApplicativeImpl e renaming (ap-map to map)
    }
  
  makeApplicative : (e : Level) → Applicative {ℓ = e} ⟦ Con ⟧ _≈_
  makeApplicative e = record {
       isApplicative = makeIsApplicative e
    }

-- Terminal morphism
! : {ℓ : Level} {X : Set ℓ} → X → ⊤ {ℓ = ℓ}
! _ = tt

-- Given an Applicative instance on ⟦ Con ⟧ with
-- the same Functor instance,
-- extract Action out of Applicative. 
module _ {s} {p} {Con : Container s p} (applicative : Applicative ⟦ Con ⟧ _≈_) where
  open Container Con renaming (Shape to S; Position to P)
  open Applicative applicative
  
  F : Set p → Set (s ⊔ p)
  F = ⟦ Con ⟧
  
  private
    module ≈-Reasoning {A : Set p} =
      Reasoning (≈-setoid{Con = Con} A)
    module props = properties applicative
    open IsEquivalence {{...}}

  -- The given applicative instance has "standard" <$>
  Canonical<$> : Set (s ⊔ suc p)
  Canonical<$> = ∀ {A B : Set p} {x : S} {f : A -> B} {g : P x → A} →
    f <$> (x , g) ≈ (x , f ∘′ g)
  
  record ExtractedAction : Set (suc (s ⊔ p)) where
    field
      rawAction : RawAction Con
    
    open RawAction rawAction hiding (S; P) public

    field
      pure-nf : ∀ {A} {a : A} → pure a ≈ (ε , const a)
      <*>-nf : ∀ {A B} {x y : S} {f : P x → A → B} {g : P y → A} →
        (x , f) <*> (y , g) ≈ (x · y , λ p → f (ϕleft p) (g (ϕright p)))
      
      -- <$>-nf is actually redundant because it follows from the above two -nf
      -- properties and IsApplicative.
      -- But we will require <$>-nf to do extractAction below
      -- to construct ExtractedAction, thus including it here is
      -- easier than proving it again when using ExtractedAction.
      <$>-nf : Canonical<$>  

  extractAction : Canonical<$> → ExtractedAction
  extractAction <$>-nf = record {
      rawAction = rawAction;
      pure-nf = pure-nf;
      <*>-nf = <*>-nf;
      <$>-nf = <$>-nf
    }
    where
      eps : ∀ { A : Set p } (a : A) → S
      eps a = proj₁ (pure a)

      dot : ∀ {A B : Set p} → (x y : S) (f : P x → A → B) (g : P y → A) → S
      dot x y f g = proj₁ ((x , f) <*> (y , g))

      ε : S
      ε = eps tt

      pure-nf : ∀ {A} {a : A} → pure a ≈ (ε , const a)
      pure-nf {a = a} =
        begin
          pure a
        ≈⟨ props.pure-naturality _ _ ⟨
          const a <$> pure tt
        ≈⟨ refl ⟩
          const a <$> (ε , _)
        ≈⟨ <$>-nf ⟩
          (ε , const a)
        ∎
        where open ≈-Reasoning

      _·_ : S → S → S
      _·_ x y = dot x y pair id

      ϕ : ∀ {x y : S} → P (x · y) → P x × P y
      ϕ {x = x} {y = y} = proj₂ ((x , pair) <*> (y , id))
      
      ϕleft : ∀ {x y : S} → P (x · y) → P x
      ϕleft p = proj₁ (ϕ p)

      ϕright : ∀ {x y : S} → P (x · y) → P y
      ϕright p = proj₂ (ϕ p)

      <*>-nf : ∀ {A B : Set p} {x y : S} {f : P x → A → B} {g : P y → A} →
        (x , f) <*> (y , g) ≈ (x · y , λ p → f (ϕleft p) (g (ϕright p)))
      <*>-nf {x = x} {y = y} {f = f} {g = g} =
        begin
          (x , f) <*> (y , g)
        ≈⟨ props.<*>-cong₂ <$>-nf ⟨
          (x , f) <*> (g <$> (y , id))
        ≈⟨ props.naturality₂ _ _ _ ⟨
          (_∘′ g <$> (x , f)) <*> (y , id)
        ≈⟨ props.<*>-cong₁ <$>-nf ⟩
          (x , λ px py → f px (g py)) <*> (y , id)
        ≈⟨ refl ⟩
          (x , λ px py → fg (pair px py)) <*> (y , id)
        ≈⟨ props.<*>-cong₁ <$>-nf ⟨
          fg ∘′_ <$> (x , pair) <*> (y , id)
        ≈⟨ props.naturality₁ _ _ _ ⟨
          fg <$> ((x , pair) <*> (y , id))
        ≈⟨ refl ⟩
          fg <$> (x · y , ϕ)
        ≈⟨ <$>-nf ⟩
          (x · y , fg ∘′ ϕ)
        ≈⟨ refl ⟩
          (x · y , λ p → f (ϕleft p) (g (ϕright p)))
        ∎
        where
          fg : P x × P y → _
          fg (px , py) = f px (g py)
          open ≈-Reasoning

      rawAction : RawAction Con
      rawAction = record { ε = ε; _·_ = _·_; ϕleft = ϕleft; ϕright = ϕright }
  
  reproveIsAction :
    ∀ (ext : ExtractedAction) (let raw = ext .ExtractedAction.rawAction)
    → IsAction Con raw
  reproveIsAction ext = record {isActionImpl}
    where
      module isActionImpl where
        open ExtractedAction ext

        open Pointwise

        open import Function renaming (_∋_ to infix 5 _∋_)

        unfolded-left-id : ∀ (x : S) → F (P x) ∋ (ε · x , λ p → ϕright p) ≈ (x , id)
        unfolded-left-id x =
          begin
            (ε · x , λ p → ϕright p)
          ≈⟨ <*>-nf ⟨
            (ε , const id) <*> (x , id)
          ≈⟨ props.<*>-cong₁ pure-nf ⟨
            pure id <*> (x , id)
          ≈⟨ props.identity _ ⟩
            (x , id)
          ∎
          where
            open ≈-Reasoning

        unfolded-right-id : ∀ (x : S) → F (P x) ∋ (x · ε , ϕleft) ≈ (x , id)
        unfolded-right-id x =
          begin
            (x · ε , λ p → ϕleft p)
          ≈⟨ <*>-nf ⟨
            (x , const) <*> (ε , const tt)
          ≈⟨ props.<*>-cong₂ pure-nf ⟨
            (x , const) <*> pure tt
          ≈⟨ interchange _ _ ⟩
            (λ k → k tt) <$> (x , const)
          ≈⟨ <$>-nf ⟩
            (x , id)
          ∎
          where
            open ≈-Reasoning

        unfolded-assoc : ∀ (x y z : S) →
          F (P x × P y × P z) ∋
          ((x · y) · z , λ p → ϕleft (ϕleft p) , ϕright (ϕleft p) , ϕright p)
            ≈
          (x · (y · z) , λ p → ϕleft p , ϕleft (ϕright p) , ϕright (ϕright p))
        unfolded-assoc x y z =
          begin
            ((x · y) · z , λ p → ϕleft (ϕleft p) , ϕright (ϕleft p) , ϕright p)
          ≈⟨ lhs ⟨
            _∘′_ <$> (x , pair) <*> (y , pair) <*> (z , id)
          ≈⟨ composition (x , pair) (y , pair) (z , id) ⟩
            (x , pair) <*> ((y , pair) <*> (z , id))
          ≈⟨ rhs ⟩
            (x · (y · z) , λ p → ϕleft p , ϕleft (ϕright p) , ϕright (ϕright p))
          ∎
          where
            open ≈-Reasoning

            lhs : F (P x × P y × P z) ∋ _ ≈ _
            lhs =
              begin
                _∘′_ <$> (x , pair) <*> (y , pair) <*> (z , id)
              ≈⟨ props.<*>-cong₁ (props.<*>-cong₁ <$>-nf) ⟩
                (x , _) <*> (y , pair) <*> (z , id)
              ≈⟨ props.<*>-cong₁ <*>-nf ⟩
                (x · y , _) <*> (z , id)
              ≈⟨ <*>-nf ⟩
                ((x · y) · z , λ p → ϕleft (ϕleft p) , ϕright (ϕleft p) , ϕright p)
              ∎
            rhs : F (P x × P y × P z) ∋ _ ≈ _
            rhs =
              begin
                (x , pair) <*> ((y , pair) <*> (z , id))
              ≈⟨ props.<*>-cong₂ <*>-nf ⟩
                (x , pair) <*> (y · z , _)
              ≈⟨ <*>-nf ⟩
                (x · (y · z) , λ p → ϕleft p , ϕleft (ϕright p) , ϕright (ϕright p))
              ∎

        isMonoid : IsMonoid _≡_ _·_ ε
        isMonoid = impl
          where
            open import Algebra.Structures using (IsMonoid; IsSemigroup; IsMagma)
            open IsMonoid
            open IsSemigroup
            open IsMagma
            impl : IsMonoid _≡_ _·_ ε
            impl .isSemigroup .isMagma .isEquivalence = ≡.isEquivalence
            impl .isSemigroup .isMagma .∙-cong = ≡.cong₂ _
            impl .isSemigroup .assoc x y z = unfolded-assoc x y z .shape
            impl .identity .proj₁ x = unfolded-left-id x .shape
            impl .identity .proj₂ x = unfolded-right-id x .shape
        
        open IsMonoid isMonoid

        lift≡ : {x y : S} → (x ≡ y) → P x → P y
        lift≡ = ≡.subst P

        lift≡' : {x y : S} → (x ≡ y) → P y → P x
        lift≡' eq = ≡.subst P (≡.sym eq)

        ϕleft-id : ∀ (x : S) → (p : P (x · ε)) → ϕleft p ≡ lift≡ (identityʳ x) p
        ϕleft-id x = unfolded-right-id x .position

        ϕright-id : (x : S) → ϕright ≗ lift≡ (identityˡ x)
        ϕright-id x = unfolded-left-id x .position
        
        ϕassoc : (x y z : S) (p : P ((x · y) · z))
          → (let eq = assoc x y z)
          → (ϕleft (ϕleft p) ≡ ϕleft (lift≡ eq p))
           × (ϕright (ϕleft p) ≡ ϕleft (ϕright (lift≡ eq p)))
           × (ϕright p ≡ ϕright (ϕright (lift≡ eq p)))
        ϕassoc x y z p = Prod.map₂ ,-injective (,-injective eq123)
          where
            eq123 = unfolded-assoc x y z .position p 

        ϕleft-homo : (x y z : S)
          → ϕleft ∘ ϕleft ≗ ϕleft ∘ lift≡ (assoc x y z)
        ϕleft-homo x y z p = ϕassoc x y z p .proj₁
        
        ϕright-homo : (x y z : S)
          → ϕright ∘ ϕright ≗ ϕright ∘ lift≡' (assoc x y z)
        ϕright-homo x y z p = begin
              ϕright (ϕright p)
            ≡⟨ ≡.cong (ϕright ∘′ ϕright) (≡.subst-subst-sym {P = P} eq) ⟨
              ϕright (ϕright (lift≡ eq (lift≡' eq p)))
            ≡⟨ ϕassoc x y z (lift≡' eq p) .proj₂ .proj₂ ⟨
              ϕright (lift≡' eq p)
            ∎
          where
            open ≡.≡-Reasoning
            eq = assoc x y z
        
        ϕinterchange : (x y z : S)
          → ϕright ∘ ϕleft ≗ ϕleft ∘ ϕright ∘ lift≡ (assoc x y z)
        ϕinterchange x y z p = ϕassoc x y z p .proj₂ .proj₁