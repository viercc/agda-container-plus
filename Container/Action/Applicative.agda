{-# OPTIONS --without-K --safe #-}

module Container.Action.Applicative where

open import Level

open import Function.Base using (case_of_)
open import Function using (_∘_; id; _$_; const)

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

open import Algebra using (Op₂; RawMonoid; IsMonoid; Monoid)

open import Effect.Functor
open import Effect.Applicative
open import Effect.Functor.Law
open import Effect.Applicative.Law

open import Container.Action
open import Container.Functor

private
  variable
    s p e : Level

rawApplicative⟦_,_⟧ : (Con : Container s p) → (RawAction Con)
  → {e : Level} → RawApplicative {f = e} (⟦ Con ⟧)
rawApplicative⟦_,_⟧ Con raw {e} = record {reifiedApplicative}
  where
    open RawAction raw
    open Prod using (_,_)

    module reifiedApplicative where
      variable
        A B C : Set e
      
      rawFunctor = rawFunctor⟦ Con ⟧
      pure : A → ⟦ Con ⟧ A
      pure a = (ε , const a)

      _<*>_ : ⟦ Con ⟧ (A → B) → ⟦ Con ⟧ A → ⟦ Con ⟧ B
      _<*>_ (x , f) (y , g) = (x · y , λ (i : P (x · y)) → f (ϕleft x y i) (g (ϕright x y i)))

≡-cong₃ : ∀ {ℓ ℓ′ : Level} {X Y Z : Set ℓ} {R : Set ℓ′}
  → (f : X → Y → Z → R)
  → {x1 x2 : X} → (x1 ≡ x2)
  → {y1 y2 : Y} → (y1 ≡ y2)
  → {z1 z2 : Z} → (z1 ≡ z2)
  → (f x1 y1 z1 ≡ f x2 y2 z2)
≡-cong₃ f P.refl P.refl P.refl = P.refl

-- IsAction proves IsApplicative
isApplicative⟦_,_⟧ :
  (Con : Container s p) (raw : RawAction Con) 
  → IsAction Con raw → {e : Level} → IsApplicative {ℓ = e} ⟦ Con ⟧ rawApplicative⟦ Con , raw ⟧
isApplicative⟦_,_⟧ Con raw proof {e} = record{isApplicative} where
  open RawAction raw
  open RawApplicative {f = e} rawApplicative⟦ Con , raw ⟧
  
  open Prod using (proj₁; proj₂; _,_)
  
  module isApplicative where
    variable
      A B C : Set e
    
    open IsAction proof
    isFunctor = isFunctor⟦ Con ⟧
    open IsFunctor isFunctor
    
    F : Set _ → Set _
    F = ⟦ Con ⟧
    
    ap-cong : ∀ {u₁ u₂ : F (A → B)} {v₁ v₂ : F A}
      → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (u₁ <*> v₁ ≈ u₂ <*> v₂)
    ap-cong {u₁ = x , f1} {u₂ = _ , f2} {v₁ = y , g1} {v₂ = _ , g2} (Pw P.refl f≗) (Pw P.refl g≗) =
      let
        fg≗ p =
          P.trans
            (P.cong-app (f≗ (ϕleft x y p)) _)
            (P.cong (f2 (ϕleft x y p)) (g≗ (ϕright x y p)))           
      in Pw P.refl fg≗

    ap-map : ∀ (f : A → B) (v : F A) → pure f <*> v ≈ f <$> v
    ap-map f (y , g) = Pw (identityˡ y) (λ p → P.cong (f ∘ g) (ϕright-id y p))

    ap-homomorphism : ∀ (f : A → B) (x : A) → pure f <*> pure x ≈ pure (f x)
    ap-homomorphism f x = Pw (identityˡ ε) (λ p → P.refl)

    ap-interchange : ∀ (u : F (A → B)) (y : A) → u <*> pure y ≈ (λ f → f y) <$> u
    ap-interchange (x , f) y = Pw (identityʳ x) (λ p → P.cong (λ q → f q y) (ϕleft-id x p))

    ap-composition : ∀ (u : F (B → C)) (v : F (A → B)) (w : F A)
      → comp <$> u <*> v <*> w ≈ u <*> (v <*> w)
    ap-composition (x , f) (y , g) (z , h) =
      Pw (assoc x y z) fgh-equality
      where
        fgh-equality : _
        fgh-equality p =
          ≡-cong₃ (λ p₁ p₂ p₃ → f p₁ (g p₂ (h p₃)))
            (ϕleft-homo x y z p)
            (ϕinterchange x y z p)
            (ϕright-homo' x y z p)