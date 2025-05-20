{-# OPTIONS --without-K --safe #-}

open import Level

open import Function using (_∘′_; id; const)

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product as Prod
  using (Σ; _×_; _,_; proj₁; proj₂)
  renaming (_,′_ to pair)

open import Data.Product.Properties
  using (,-injective)

open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core
open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)

open import Algebra using (Op₂; RawMonoid; IsMonoid; Monoid)

open import Effect.Functor
open import Effect.Applicative
open import Effect.Functor.Law
open import Effect.Applicative.Law
open import Effect.Applicative.Properties

open import Container.Algebra.Action
open import Container.Effect.Functor using (_≈_; ≈-isEquivalence; ≈-setoid)

module Container.Effect.Applicative.ToAction {s p : Level} {Con : Container s p} where

open Container Con renaming (Shape to S; Position to P)

private
  -- ⟦ Con ⟧ is level-polymorphic:
  -- ⟦ Con ⟧ : {e} → Set e → Set (s ⊔ p ⊔ e)
  -- 
  -- but we only care {e = p} case for this module.
  F : Set p → Set (s ⊔ p)
  F = ⟦ Con ⟧

  module ≈-Reasoning {A : Set p} =
    Reasoning (≈-setoid{Con = Con} A)
  open IsEquivalence {{...}}

-- Extracts RawAction from RawApplicative.

module _ (rawApplicative : RawApplicative F) where
  open RawApplicative rawApplicative
  
  -- Define operators (ε; _·_; ϕleft; ϕright) as
  -- projections of certain Applicative operations.
  
  private
    ε : S
    ε = proj₁ (pure tt)

    _·_ : S → S → S
    _·_ x y = proj₁ ((x , pair) <*> (y , id))

    ϕ : ∀ {x y : S} → P (x · y) → P x × P y
    ϕ {x = x} {y = y} = proj₂ ((x , pair) <*> (y , id))
    
    ϕleft : ∀ {x y : S} → P (x · y) → P x
    ϕleft p = proj₁ (ϕ p)

    ϕright : ∀ {x y : S} → P (x · y) → P y
    ϕright p = proj₂ (ϕ p)

  extractRawAction : RawAction Con
  extractRawAction = record { ε = ε; _·_ = _·_; ϕleft = ϕleft; ϕright = ϕright }

Canonical<$> : (∀ {A B : Set p} → (A → B) → F A → F B) → Set (s ⊔ suc p)
Canonical<$> _<$>_ = ∀ {A B} {f : A → B} {x : S} {g : P x → A}
  → f <$> (x , g) ≈ (x , f ∘′ g)

-- Let's say a RawAction is a "Correct" extraction of a RawApplicative
-- if it can reproduce (_<$>_; pure; _<*>_) up to _≈_ relation.
record Correctness (rawApplicative : RawApplicative F) (rawAction : RawAction Con) : Set (suc (s ⊔ p)) where
  open RawApplicative rawApplicative
  open RawAction rawAction

  field
    <$>-nf : Canonical<$> _<$>_
    pure-nf : ∀ {A} {a : A} → pure a ≈ (ε , const a)
    <*>-nf : ∀ {A B} {x y : S} {f : P x → A → B} {g : P y → A} →
      (x , f) <*> (y , g) ≈ (x · y , λ p → f (ϕleft p) (g (ϕright p)))

module _ (applicative : Applicative ⟦ Con ⟧ _≈_) where
  open Applicative applicative
  
  private
    module props = properties applicative

  -- Correctness ∧ Applicative implies IsAction
  Correct→IsAction :
    ∀ (rawAction : RawAction Con) (correct : Correctness rawApplicative rawAction)
      → IsAction Con rawAction 
  Correct→IsAction rawAction correct = record {isActionImpl}
    where
      module isActionImpl where
        open RawAction rawAction
        open Correctness correct

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

        open import Algebra.Structures.PatternSynonyms

        isMonoid : IsMonoid _≡_ _·_ ε
        isMonoid =
          mkIsMonoid ≡.isEquivalence (≡.cong₂ _·_)
            (λ x y z → unfolded-assoc x y z .shape)
            (λ x → unfolded-left-id x .shape)
            (λ x → unfolded-right-id x .shape)
        
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
          → ϕright ≗ ϕright ∘ ϕright ∘ lift≡ (assoc x y z)
        ϕright-homo x y z p = ϕassoc x y z p .proj₂ .proj₂
        
        ϕinterchange : (x y z : S)
          → ϕright ∘ ϕleft ≗ ϕleft ∘ ϕright ∘ lift≡ (assoc x y z)
        ϕinterchange x y z p = ϕassoc x y z p .proj₂ .proj₁

module _ (applicative : Applicative F _≈_) where
  open Applicative applicative
  
  private
    module props = properties applicative

  -- Assuming <$> is the canonical one, extractRawAction is correct.
  correctness : Canonical<$> _<$>_ → Correctness rawApplicative (extractRawAction rawApplicative)
  correctness <$>-nf = record {
      <$>-nf = <$>-nf;
      pure-nf = pure-nf;
      <*>-nf = <*>-nf
    }
    where
      open RawAction (extractRawAction rawApplicative)

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
          fg <$> (x · y , λ p → pair (ϕleft p) (ϕright p))
        ≈⟨ <$>-nf ⟩
          (x · y , λ p → f (ϕleft p) (g (ϕright p)))
        ∎
        where
          fg : P x × P y → _
          fg (px , py) = f px (g py)
          open ≈-Reasoning

   