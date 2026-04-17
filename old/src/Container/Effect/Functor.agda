{-# OPTIONS --without-K --safe #-}

module Container.Effect.Functor where

open import Level

open import Function using (_∘_; id; _$_)

open import Relation.Binary using (Rel; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as ≡
    using (_≡_)

open import Data.Product as Prod using (proj₁; proj₂; _,_)

open import Data.Container.Core
import Data.Container.Properties as ContProp
open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to Pw)
import Data.Container.Relation.Binary.Equality.Setoid as CSetoid

open import Effect.Functor
open import Effect.Functor.Law

private
  variable
    s p : Level

module _ {Con : Container s p} where
  infix 3 _≈_

  _≈_ : ∀ {e} {A : Set e} → Rel (⟦ Con ⟧ A) (s ⊔ p ⊔ e)
  _≈_ {A = A} = CSetoid.Eq (≡.setoid A) Con
  
  instance
    ≈-isEquivalence : {e : Level} {A : Set e} → IsEquivalence (_≈_ {A = A})
    ≈-isEquivalence {A = A} = CSetoid.isEquivalence (≡.setoid A) Con
  
  ≈-setoid : {e : Level} (A : Set e) → Setoid (s ⊔ p ⊔ e) (s ⊔ p ⊔ e)
  ≈-setoid A = CSetoid.setoid (≡.setoid A) Con

module _ (Con : Container s p) where
  
  makeRawFunctor : (e : Level) → RawFunctor {ℓ = e} (⟦ Con ⟧) 
  makeRawFunctor e = record { _<$>_ = map }
  
  private 
    module isFunctor (e : Level) where
      open RawFunctor (makeRawFunctor e)

      <$>-cong : ∀  {A B : Set e} (f : A → B) {u₁ u₂ : ⟦ Con ⟧ A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
      <$>-cong f (Pw s≡ pos≗) = Pw s≡ (λ p → ≡.cong f (pos≗ p))

      <$>-id : ∀ {A : Set e} (x : ⟦ Con ⟧ A) → (id <$> x ≈ x)
      <$>-id {A = A} x = ContProp.map-identity (≡.setoid A) x

      <$>-∘  : ∀ {A B C : Set e} (f : B → C) (g : A → B) (x : ⟦ Con ⟧ A)
        → (f <$> (g <$> x) ≈ (f ∘ g) <$> x)
      <$>-∘ {C = C} f g x = ContProp.map-compose (≡.setoid C) f g x

  makeIsFunctor : (e : Level) → IsFunctor {ℓ = e} ⟦ Con ⟧ _≈_ (makeRawFunctor e)
  makeIsFunctor e = record {isFunctor e}
 
  makeFunctor : (e : Level) → Functor {ℓ = e} ⟦ Con ⟧ _≈_
  makeFunctor e = record { isFunctor = makeIsFunctor e }
