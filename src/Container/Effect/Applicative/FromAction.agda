{-# OPTIONS --without-K --safe #-}

open import Level

open import Function using (_∘′_; id; _$_; const)

open import Data.Product as Prod
  using (_,_; proj₁; proj₂)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)

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
open import Container.Effect.Functor

module Container.Effect.Applicative.FromAction {s p : Level} {Con : Container s p} where
  
-- Make RawApplicative out of RawAction
module _ (raw : RawAction Con) where
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

-- Make Applicative out of Action
module _ (action : Action Con) where
  open Action action
  
  private
    ≡-cong₃ : ∀ {a e : Level} {X Y Z : Set a} {R : Set e}
      → (f : X → Y → Z → R)
      → {x1 x2 : X} → (x1 ≡ x2)
      → {y1 y2 : Y} → (y1 ≡ y2)
      → {z1 z2 : Z} → (z1 ≡ z2)
      → (f x1 y1 z1 ≡ f x2 y2 z2)
    ≡-cong₃ f ≡.refl ≡.refl ≡.refl = ≡.refl

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
      ap-map f (y , g) = Pw (identityˡ y) (λ p → ≡.cong (f ∘′ g) (ϕright-id y p))

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
              (ϕright-homo x y z p)

  makeIsApplicative : (e : Level) → IsApplicative ⟦ Con ⟧ _≈_ (makeRawApplicative rawAction e)
  makeIsApplicative e = record{
      isApplicativeImpl e renaming (ap-map to map)
    }
  
  makeApplicative : (e : Level) → Applicative {ℓ = e} ⟦ Con ⟧ _≈_
  makeApplicative e = record {
       isApplicative = makeIsApplicative e
    }
