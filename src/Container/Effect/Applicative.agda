{-# OPTIONS --without-K --safe #-}

module Container.Effect.Applicative where

open import Level

open import Function.Base using (case_of_)
open import Function using (_∘_; _∘′_; id; _$_; const)

import Data.Product as Prod

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)

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

-- Given an Applicative instance on ⟦ Con ⟧ with
-- the canonical Functor instance as its "superclass",
-- extract Action out of Applicative. 
extractAction : {Con : Container s p}
  → (applicative : Applicative {ℓ = p} ⟦ Con ⟧)
  → (Applicative.functor applicative ≡ makeFunctor Con p)
  → Action Con
extractAction {Con = C} applicative ≡.refl = _