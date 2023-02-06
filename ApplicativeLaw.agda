module ApplicativeLaw where

open import Level
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.PropositionalEquality
    using () renaming (_≡_ to infix 3 _≡_)

open import Function using (_∘_; id; _$_)
open import Effect.Functor
open import Effect.Applicative
open import FunctorLaw

private
  variable
    ℓ ℓ′ ℓ″ : Level
    A B C D : Set ℓ

comp : ∀ {a} {A : Set a} {b} {B : Set b} {c} {C : Set c} →
    (B -> C) -> (A -> B) -> (A -> C)
comp f g = f ∘ g

record IsApplicative (F : Set ℓ → Set ℓ′) (raw : RawApplicative F) : Set (suc (ℓ ⊔ ℓ′)) where
  open RawApplicative raw

  field
    isFunctor : IsFunctor F rawFunctor

  open IsFunctor isFunctor public

  field
    ap-cong : ∀ {u₁ u₂ : F (A → B)} {v₁ v₂ : F A} → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (u₁ <*> v₁ ≈ u₂ <*> v₂)
    
    ap-map : ∀ (f : A → B) (v : F A) → pure f <*> v ≈ f <$> v
    ap-homomorphism : ∀ (f : A → B) (x : A) → pure f <*> pure x ≈ pure (f x)
    ap-interchange : ∀ (u : F (A → B)) (y : A) → u <*> pure y ≈ pure (λ f → f y) <*> u
    ap-composition : ∀ (u : F (B → C)) (v : F (A → B)) (w : F A)
      → comp <$> u <*> v <*> w ≈ u <*> (v <*> w)
  
  module Consequences where
    open IsEquivalence {{...}}
    
    pure-cong : ∀ {x y : A} → x ≡ y → pure x ≈ pure y
    pure-cong x≡y = reflexive (P.cong pure x≡y)
    
    zipWith-cong : ∀ (f : A → B → C) {u₁ u₂ : F A} {v₁ v₂ : F B}
      → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (zipWith f u₁ v₁ ≈ zipWith f u₂ v₂)
    zipWith-cong f {u₁} {u₂} {v₁} {v₂} u≈ v≈ = ap-cong (map-cong f u≈) v≈

    ap-cong₁ : ∀ {u₁ u₂ : F (A → B)} {v : F A} → (u₁ ≈ u₂) → (u₁ <*> v ≈ u₂ <*> v)
    ap-cong₁ u≈ = ap-cong u≈ refl

    ap-cong₂ : ∀ {u : F (A → B)} {v₁ v₂ : F A} → (v₁ ≈ v₂) → (u <*> v₁ ≈ u <*> v₂)
    ap-cong₂ v≈ = ap-cong refl v≈

    ap-identity : ∀ (v : F A) → pure id <*> v ≈ v
    ap-identity v = trans (ap-map id v) (map-id v)
    
    pure-naturality : ∀ (f : A → B) (x : A) → f <$> pure x ≈ pure (f x)
    pure-naturality f x = trans (sym (ap-map f (pure x))) (ap-homomorphism f x)
    
    ap-naturality₁ : ∀ (f : B → C) (u : F (A → B)) (v : F A)
        → f <$> (u <*> v) ≈ comp f <$> u <*> v
    ap-naturality₁ f u v =
      trans (sym (ap-map f (u <*> v))) $
      trans (sym (ap-composition (pure f) u v)) $
      trans (ap-cong₁ (ap-cong₁ (pure-naturality comp f))) $
      ap-cong₁ (ap-map (comp f) u)
    
    ap-naturality₂ : ∀ (g : A → B) (u : F (B → C)) (v : F A)
        → (λ f → comp f g) <$> u <*> v ≈ u <*> (g <$> v)
    ap-naturality₂ g u v =
      trans (ap-cong₁ (sym aux)) $
      trans (ap-composition u (pure g) v) $
      ap-cong₂ (ap-map g v)
      where
        aux : (comp <$> u) <*> pure g ≈ (λ f → comp f g) <$> u
        aux =
          trans (ap-interchange (comp <$> u) g) $
          trans (ap-map (λ r → r g) (comp <$> u)) $
          map-∘ ((λ r → r g)) comp u
