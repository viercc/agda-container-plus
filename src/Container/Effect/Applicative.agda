{-# OPTIONS --without-K --safe #-}

module Container.Effect.Applicative where

open import Level

open import Function using (_∘_; _∘′_; id; _$_; const)

open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Data.Product as Prod
  using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Properties
  using (,-injectiveˡ)

open import Relation.Binary using (Setoid; IsEquivalence)
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
  open Prod using (proj₁; proj₂; _,_)
  
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

  makeIsApplicative : (e : Level) → IsApplicative ⟦ Con ⟧ (makeRawApplicative rawAction e)
  makeIsApplicative e = record{
      isApplicativeImpl e renaming (ap-map to map)
    }
  
  makeApplicative : (e : Level) → Applicative {ℓ = e} ⟦ Con ⟧
  makeApplicative e = record {
       isApplicative = makeIsApplicative e
    }

-- Terminal morphism
! : {ℓ : Level} {X : Set ℓ} → X → ⊤ {ℓ = ℓ}
! _ = tt

-- Given an Applicative instance on ⟦ Con ⟧ with
-- the canonical Functor instance as its "superclass",
-- extract Action out of Applicative. 

extractAction : {Con : Container s p}
  → (applicative : Applicative {ℓ = p} ⟦ Con ⟧)
  → (Applicative.functor applicative ≡ makeFunctor Con p)
  → UIP (Shape Con)
  → Action Con
extractAction {s} {p} {Con = Con} applicative ≡.refl uip = record { rawAction = rawAction; isAction = isAction }
  where
    open Container Con renaming (Shape to S; Position to P)
    open Applicative applicative
    open IsEquivalence {{...}}

    module props = properties ⟦ Con ⟧ applicative

    ε : ∀ { A : Set p} { a : A } → S
    ε {a = a} = proj₁ (pure a)

    ε₀ : S
    ε₀ = ε {a = tt}

    _·_ : ∀ {A B : Set p} → (x y : S) {f : P x → A → B} {g : P y → A} → S
    _·_ x y  {f = f} {g = g} = proj₁ ((x , f) <*> (y , g))

    _·₀_ : S → S → S
    _·₀_ x y = _·_ x y {f = const id} {g = !}

    irrelevant-ε : ∀ {A : Set p} {a : A} → ε₀ ≡ ε {a = a}
    irrelevant-ε {a = a} = sym (props.pure-naturality ! a) .Pointwise.shape

    irrelevant-· : ∀ {A B : Set p} (x y : S) {f : P x → A → B} {g : P y → A} 
      → x ·₀ y ≡ _·_ x y {f = f} {g = g}
    irrelevant-· x y {f = f} {g = g} = sym proof .Pointwise.shape
      where
        u = x , f
        v = y , g

        proof : ! <$> (u <*> v) ≈ (x , const id) <*> (y , const tt)
        proof = begin
            ! <$> (u <*> v)
          ≈⟨ props.naturality₁ ! u v ⟩
            const ! <$> u <*> v
          ≈⟨ <*>-cong (<$>-∘ (_∘′ !) (const id) u) refl ⟨
            (_∘′ !) <$> (const id <$> u) <*> v
          ≈⟨ props.naturality₂ ! (const id <$> u) v ⟩
            (const id <$> u) <*> (! <$> v)
          ≈⟨ refl ⟩
            ((x , const id) <*> (y , const tt))
          ∎
          where open props.≈-Reasoning
    
    ϕleft : ∀ {x y : S} → P (x ·₀ y) → P x
    ϕleft {x = x} {y = y} p = proj₂ ((x , const) <*> (y , !)) (≡.subst P (irrelevant-· x y) p)

    ϕright : ∀ {x y : S} → P (x ·₀ y) → P y
    ϕright {x = x} {y = y} p = proj₂ ((x , const id) <*> (y , id)) (≡.subst P (irrelevant-· x y) p)

    rawAction : RawAction Con
    rawAction = record { ε = ε₀; _·_ = _·₀_; ϕleft = ϕleft; ϕright = ϕright }
    
    module _ where
      -- (S; ε₀; _·₀_) is a Monoid

      S-identityˡ : ∀ (x : S) → ε₀ ·₀ x ≡ x
      S-identityˡ x = ≡.trans (≡.cong (_·₀ x) irrelevant-ε) (proof .Pointwise.shape)
        where
          proof : pure id <*> (x , !) ≈ (x , !)
          proof = props.identity _
      
      S-identityʳ : ∀ (x : S) → x ·₀ ε₀ ≡ x
      S-identityʳ x = interchange (x , const id) tt .Pointwise.shape

      S-assoc : ∀ (x y z : S) → (x ·₀ y) ·₀ z ≡ x ·₀ (y ·₀ z)
      S-assoc x y z = ≡.trans (≡.cong (_·₀ z) (irrelevant-· x y)) (proof .Pointwise.shape) 
        where
          u = (x , const id)
          v = (y , const id)
          w = (z , !)

          proof : _∘′_ <$> u <*> v <*> w ≈ u <*> (v <*> w)
          proof = composition u v w

      open import Algebra.Structures using (IsMonoid; IsSemigroup; IsMagma)
      open IsMonoid
      open IsSemigroup
      open IsMagma
      S-isMonoid : IsMonoid _≡_ _·₀_ ε₀
      S-isMonoid .isSemigroup .isMagma .isEquivalence = ≡.isEquivalence
      S-isMonoid .isSemigroup .isMagma .∙-cong = ≡.cong₂ _
      S-isMonoid .isSemigroup .assoc = S-assoc
      S-isMonoid .identity = S-identityˡ , S-identityʳ

    private
      module isActionImpl where
        isMonoid : IsMonoid _≡_ _·₀_ ε₀
        isMonoid = S-isMonoid

        open IsMonoid isMonoid

        lift≡ : {x y : S} → (x ≡ y) → P x → P y
        lift≡ = ≡.subst P

        lift≡' : {x y : S} → (x ≡ y) → P y → P x
        lift≡' eq = ≡.subst P (≡.sym eq)

        ϕleft-id : ∀ (x : S) → (p : P (x ·₀ ε₀)) → ϕleft p ≡ lift≡ (identityʳ x) p
        ϕleft-id x = λ p → begin
            ϕleft p
          ≡⟨⟩
            proj₂ ((x , const) <*> pure tt) (lift≡ irrelevance p)
          ≡⟨ proof-pos (lift≡ irrelevance p) ⟩
            lift≡ proof-shape (lift≡ irrelevance p)
          ≡⟨ ≡.subst-subst irrelevance {p = p} ⟩
            lift≡ (≡.trans irrelevance proof-shape) p
          ≡⟨ ≡.cong (λ eq → lift≡ eq p) (uip _ _) ⟩
            lift≡ (identityʳ x) p
          ∎
          where
            open ≡.≡-Reasoning

            irrelevance : x ·₀ ε₀ ≡ _·_ x ε₀ {f = const} {g = !}
            irrelevance = irrelevant-· x ε₀

            proof : (x , const) <*> pure tt ≈ (x , id)
            proof = interchange (x , const) tt

            proof-shape : x · ε₀ ≡ x
            proof-shape = proof .Pointwise.shape

            proof-pos : ∀ (p : P (x · ε₀)) →
              proj₂ ((x , const) <*> pure tt) p ≡ lift≡ proof-shape p
            proof-pos = proof .Pointwise.position

        ϕright-id : (x : S) → ϕright ≗ lift≡ (identityˡ x)
        ϕright-id x = λ p → begin
            ϕright p
          ≡⟨⟩
            proj₂ (pure id <*> (x , id)) (lift≡ irrelevance p)
          ≡⟨ proof-pos (lift≡ irrelevance p) ⟩
            lift≡ proof-shape (lift≡ irrelevance p)
          ≡⟨ ≡.subst-subst irrelevance {p = p} ⟩
            lift≡ (≡.trans irrelevance proof-shape) p
          ≡⟨ ≡.cong (λ eq → lift≡ eq p) (uip _ _) ⟩
            lift≡ (identityˡ x) p
          ∎
          where
            open ≡.≡-Reasoning

            proof : pure id <*> (x , id) ≈ (x , id)
            proof = props.identity (x , id)

            proof-shape : ε · x ≡ x
            proof-shape = proof .Pointwise.shape

            proof-pos : ∀ (p : P (ε · x)) →
              proj₂ (pure id <*> (x , id)) p ≡ lift≡ proof-shape p
            proof-pos = proof .Pointwise.position

            irrelevance = ≡.trans (≡.cong (_·₀ x) irrelevant-ε) (irrelevant-· ε x)
        
        ϕleft-homo : (x y z : S)
          → ϕleft ∘ ϕleft ≗ ϕleft ∘ lift≡ (assoc x y z)
        ϕleft-homo x y z p = _
        
        ϕright-homo : (x y z : S)
          → ϕright ∘ ϕright ≗ ϕright ∘ lift≡' (assoc x y z)
        ϕright-homo x y z p = _
        
        ϕinterchange : (x y z : S)
          → ϕright ∘ ϕleft ≗ ϕleft ∘ ϕright ∘ lift≡ (assoc x y z)
        ϕinterchange x y z p = _
    
    isAction : IsAction Con rawAction
    isAction = record {isActionImpl}