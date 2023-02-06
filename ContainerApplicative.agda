module ContainerApplicative where

open import Level

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
open import FunctorLaw
open import ApplicativeLaw

private
  variable
    s p e : Level

Eq' : (Con : Container s p) {A : Set e} → Rel (⟦ Con ⟧ A) (s ⊔ p ⊔ e)
Eq' Con {A} = CSetoid.Eq (P.setoid A) Con

isEquivalence' : (Con : Container s p) {A : Set e} → IsEquivalence (Eq' Con {A = A})
isEquivalence' Con {A} = CSetoid.isEquivalence (P.setoid A) Con

rawFunctor⟦_⟧ : (Con : Container s p) → RawFunctor {ℓ = e} (⟦ Con ⟧) 
rawFunctor⟦_⟧ Con = record { _<$>_ = map }

isFunctor⟦_⟧ : (Con : Container s p) → {e : Level} → IsFunctor {ℓ = e} ⟦ Con ⟧ (rawFunctor⟦ Con ⟧)
isFunctor⟦_⟧ Con {e} = record {isFunctor} where
  module isFunctor where
    open RawFunctor (rawFunctor⟦ Con ⟧)
    infix 3 _≈_
    
    _≈_ = Eq' {e = e} Con
    isEquivalence = isEquivalence' {e = e} Con

    map-cong : ∀  {A B : Set e} (f : A → B) {u₁ u₂ : ⟦ Con ⟧ A} → (u₁ ≈ u₂) → (f <$> u₁ ≈ f <$> u₂)
    map-cong f (Pw s≡ pos≗) = Pw s≡ (λ p → P.cong f (pos≗ p))

    map-id : ∀ {A : Set e} (x : ⟦ Con ⟧ A) → (id <$> x ≈ x)
    map-id {A = A} x = ContProp.map-identity (P.setoid A) x

    map-∘  : ∀ {A B C : Set e} (f : B → C) (g : A → B) (x : ⟦ Con ⟧ A)
      → (f <$> (g <$> x) ≈ (f ∘ g) <$> x)
    map-∘ {C = C} f g x = ContProp.map-compose (P.setoid C) f g x

-- Action of Con (Shape acting on Position): the data to define Applicative on ⟦ Con ⟧
record RawAction (Con : Container s p) : Set (s ⊔ p) where
  infixl 7 _·_

  S : Set s
  S = Shape Con

  P : S → Set p
  P = Position Con

  field 
    _·_ : Op₂ S
    ε : S
    ϕleft : (x y : S) → P (x · y) → P x
    ϕright : (x y : S) → P (x · y) → P y
  
  instance
    rawMonoid : RawMonoid s s
    rawMonoid = record { Carrier = S; _≈_ = _≡_; _∙_ = _·_; ε = ε }
  
  open RawMonoid rawMonoid using (_≉_; rawMagma) public
  
  ϕmid : (x y z : S) → P (x · y · z) → P y
  ϕmid x y z = ϕright x y ∘ ϕleft (x · y) z
  
  ϕmid' : (x y z : S) → P (x · (y · z)) → P y
  ϕmid' x y z = ϕleft y z ∘ ϕright x (y · z)

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

-- Equivalence relation defined as Pointwise ≡
infixl 3 _≗_ With_,_≗_

_≗_ : ∀ {ℓ} {X Y : Set ℓ} → Rel (X → Y) ℓ
_≗_ f g = ∀ p → f p ≡ g p

≗-isEquivalence : ∀ {ℓ} {X Y : Set ℓ} → IsEquivalence (_≗_ {X = X} {Y = Y})
≗-isEquivalence = record
  { refl = λ _ → P.refl;
    sym = λ x≗y p → P.sym (x≗y p);
    trans = λ x≗y y≗z p → P.trans (x≗y p) (y≗z p)
  }

With_,_≗_ : ∀ {ℓ} {X X' Y : Set ℓ} → X ≡ X' → (X → Y) → (X' → Y) → Set ℓ
With_,_≗_ P.refl = _≗_

-- Laws on Action Con
record IsAction (Con : Container s p) (raw : RawAction Con) : Set (s ⊔ p) where
  open RawAction raw
  
  field
    instance
      isMonoid : IsMonoid _≡_ _·_ ε
  
  open IsMonoid isMonoid renaming (∙-cong to ·-cong) public
  
  field
    ϕleft-id : (x : S) (let eq = identityʳ x)
      → With (P.cong P eq) , ϕleft x ε ≗ id
    
    ϕright-id : (x : S) (let eq = identityˡ x)
      → With (P.cong P eq) , ϕright ε x ≗ id
    
    ϕleft-homo : (x y z : S) (let eq = assoc x y z)
      → With (P.cong P eq) , ϕleft x y ∘ ϕleft (x · y) z ≗ ϕleft x (y · z)
    
    ϕright-homo : (x y z : S) (let eq = sym (assoc x y z))
      → With (P.cong P eq) , ϕright y z ∘ ϕright x (y · z) ≗ ϕright (x · y) z
    
    ϕinterchange : (x y z : S) (let eq = assoc x y z)
      → With (P.cong P eq) , ϕmid x y z ≗ ϕmid' x y z

-- IsAction proves IsApplicative
isApplicative⟦_,_⟧ : (Con : Container s p) (raw : RawAction Con)
  → {e : Level} → IsApplicative {ℓ = e} ⟦ Con ⟧ rawApplicative⟦ Con , raw ⟧
isApplicative⟦_,_⟧ Con raw {e} = record{isApplicative} where
  open RawAction raw
  open RawApplicative {f = e} rawApplicative⟦ Con , raw ⟧
  module isApplicative where
    variable
      A B C : Set e

    isFunctor = isFunctor⟦ Con ⟧

    F : Set _ → Set _
    F = ⟦ Con ⟧

    open IsFunctor {ℓ = e} isFunctor
    
    ap-cong : ∀ {u₁ u₂ : F (A → B)} {v₁ v₂ : F A} → (u₁ ≈ u₂) → (v₁ ≈ v₂) → (u₁ <*> v₁ ≈ u₂ <*> v₂)
    ap-cong u≈ v≈ = {!   !}

    ap-map : ∀ (f : A → B) (v : F A) → pure f <*> v ≈ f <$> v
    ap-map f v = {!   !}

    ap-homomorphism : ∀ (f : A → B) (x : A) → pure f <*> pure x ≈ pure (f x)
    ap-homomorphism f x = {!   !}

    ap-interchange : ∀ (u : F (A → B)) (y : A) → u <*> pure y ≈ pure (λ f → f y) <*> u
    ap-interchange u y = {!   !}

    ap-composition : ∀ (u : F (B → C)) (v : F (A → B)) (w : F A)
      → comp <$> u <*> v <*> w ≈ u <*> (v <*> w)
    ap-composition u v w = {!   !}