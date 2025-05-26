-- TODO: Re-add --safe
{-# OPTIONS --without-K #-}

-- StateLike monad, a subclass of Monomial monad
module Container.Algebra.Monad.StateLike where

open import Level

import Function as F
open F using (_∘′_; id)
import Data.Product as Prod
open Prod using (Σ; proj₁; proj₂; _,_)
open import Data.Empty
open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_)
import Data.Bool.Properties as BoolProp

open import Relation.Binary
  using (IsEquivalence; Setoid; DecidableEquality)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≢_; _≗_)
open import Relation.Nullary
  using (Dec; does; yes; no; ⌊_⌋)

open import Data.Container.Core

open import Container.Algebra.Monad.Monomial

private
  variable
    m p : Level

record RawStateLike (M : Set m) (I : Set p) : Set (m ⊔ p) where
  infixr 7 _•_
  
  field
    ε : M
    _•_ : M → (I → M) → M
    t : I → M → I

record IsStateLike (M : Set m) (I : Set p) (raw : RawStateLike M I) : Set (m ⊔ p) where
  open RawStateLike raw

  diag : M → (I → I → M) → (I → M)
  diag m w i = w i (t i m)

  zip : (I → M) → (I → I → M) → (I → M)
  zip v w i = v i • w i

  field
    •-cong₂ : ∀ {m : M} {f g : I → M} → f ≗ g → m • f ≡ m • g

    •-ε : ∀ (m : M) → m • F.const ε ≡ m
    ε-• : ∀ (m : M) → ε • F.const m ≡ m
    •-• : ∀ (m : M) (v : I → M) (w : I → I → M)
      → (m • v) • diag m w ≡ m • zip v w

    t-ε : ∀ (i : I) → t i ε ≡ i
    
    t-• : ∀ (m : M) (v : I → M)
      → (i : I)
      → t i (m • v) ≡ t (t i m) (v i)

-- StateLike is a special Monomial

module _ {M : Set m} {I : Set p} where
  toRawMonad' : RawStateLike M I → RawMonad' M I
  toRawMonad' rawSL = record {
      ε = ε;
      _•_ = _•_; 
      ql = λ _ _ i → i;
      qr = λ m _ i → t i m 
    }
    where open RawStateLike rawSL
  
  toIsMonad' : (rawSL : RawStateLike M I)
    → IsStateLike M I rawSL → IsMonad' M I (toRawMonad' rawSL)
  toIsMonad' rawSL isSL = record {
      •-cong₂ = •-cong₂;
      ql-cong₂ = λ _ _ → ≡.refl;
      qr-cong₂ = λ _ _ → ≡.refl;
      ε-• = ε-•;
      •-ε = •-ε;
      •-• = •-•;
      ql-inner-ε = λ _ _ → ≡.refl;
      qr-outer-ε = λ _ i → t-ε i;
      ql-ql = λ _ _ _ _ → ≡.refl;
      qr-ql = λ _ _ _ _ → ≡.refl;
      qr-qr = λ s v _ i → t-• s v i
    }
    where
      open RawStateLike rawSL
      open IsStateLike isSL

-- Given these two conditions:
-- 
-- * Type `I` has decidable equality
-- * There are inverse(s) of `ql ε v` for all `v : I → M`
-- 
-- A Monomial monad have isomorphic StateLike monad.

module RawMonad'+DecEq {M : Set m} {I : Set p}
  (raw : RawMonad' M I) (_≟_ : DecidableEquality I) where
  open RawMonad' raw public

  α : I → M → I → M
  α i m j = if ⌊ i ≟ j ⌋ then m else ε

  β : I → M → I → M
  β i m j = if ⌊ i ≟ j ⌋ then ε else m
  
  -- projection
  at : M → I → M
  at m i = ε • α i m

  -- Range of projections ("factors")
  FM : (i : I) → Set m
  FM i = Σ M (λ m → at m i ≡ m)

  -- Product of all factors (FM i).
  -- (we will show later that Factors of M is isomorphic to M itself)
  Factors : Set (p ⊔ m)
  Factors = (i : I) → FM i

  -- ... but only up to pointwise, proof-irrelevant equivalence relation!
  EqFactors : Factors → Factors → Set (p ⊔ m)
  EqFactors f g = ∀ (i : I) → proj₁ (f i) ≡ proj₁ (g i)

module IfLemma {ℓ} {A : Set ℓ} where
  case-apply : ∀ {b} {B : Set b}
    (cond : Bool) (f g : A → B) {x y : A}
    → (if cond then f else g) (if cond then x else y) ≡ (if cond then f x else g y)
  case-apply true  _ _ = ≡.refl
  case-apply false _ _ = ≡.refl

  case-apply₁ : ∀ {b} {B : Set b}
    (cond : Bool) (f g : A → B) {x : A}
    → (if cond then f else g) x ≡ (if cond then f x else g x)
  case-apply₁ true  _ _ = ≡.refl
  case-apply₁ false _ _ = ≡.refl

  case-apply₂ : ∀ {b} {B : Set b}
    (cond : Bool) (f : A → B) {x y : A}
    → f (if cond then x else y) ≡ (if cond then f x else f y)
  case-apply₂ true  _ = ≡.refl
  case-apply₂ false _ = ≡.refl

  if-dud : ∀ {cond : Bool} {x : A}
    → (if cond then x else x) ≡ x
  if-dud {cond = false} = ≡.refl
  if-dud {cond = true} = ≡.refl

  if-and : ∀ (cond₁ cond₂ : Bool) {x y : A}
    → (if cond₁ then (if cond₂ then x else y) else y) ≡ (if (cond₁ ∧ cond₂) then x else y)
  if-and false _ = ≡.refl
  if-and true false = ≡.refl
  if-and true true = ≡.refl

module DecEqLemma {ℓ} {I : Set ℓ} (_≟_ : DecidableEquality I) where
  infix 4 _==_

  _==_ : I → I → Bool
  _==_ x y = ⌊ x ≟ y ⌋

  dec-refl : ∀ {i : I} → (i == i) ≡ true
  dec-refl {i} with i ≟ i
  ... | yes _ = ≡.refl
  ... | no absurdity = ⊥-elim (absurdity ≡.refl)

  dec-neq : ∀ {i j : I} → (i ≢ j) → (i == j) ≡ false
  dec-neq {i} {j} i≢j with i ≟ j
  ... | yes i≡j = ⊥-elim (i≢j i≡j)
  ... | no _ = ≡.refl

  elim-if-refl : ∀ {i : I} {a} {A : Set a} {x y : A}
    → (if i == i then x else y) ≡ x
  elim-if-refl = ≡.cong (if_then _ else _) dec-refl

  rewrite-under-if : ∀ (i j : I) {a} {A : Set a} {x₁ x₂ y : A}
    → (i ≡ j → x₁ ≡ x₂) → (if i == j then x₁ else y) ≡ (if i == j then x₂ else y)
  rewrite-under-if i j rewriter with i ≟ j
  ... | yes i≡j = rewriter i≡j
  ... | no _ = ≡.refl

  ==-sym : ∀ {i j : I} → (i == j) ≡ (j == i)
  ==-sym {i} {j} with i ≟ j | j ≟ i
  ... | yes _ | yes _ = ≡.refl
  ... | yes eq | no neq = ⊥-elim (neq (≡.sym eq))
  ... | no neq | yes eq = ⊥-elim (neq (≡.sym eq))
  ... | no _ | no _ = ≡.refl

  rotate-eq : ∀ (i j k : I)
    → (i == k) ∧ (j == k) ≡ (i == j) ∧ (i == k)
  rotate-eq i j k with i ≟ k | j ≟ k | i ≟ j
  ... | no _ | _ | _ = ≡.sym (BoolProp.∧-zeroʳ _)
  ... | yes _ | yes _ | yes _ = ≡.refl
  ... | yes ≡.refl | yes ≡.refl | no i≢j = ⊥-elim (i≢j ≡.refl)
  ... | yes ≡.refl | no j≢k | yes ≡.refl = ⊥-elim (j≢k ≡.refl)
  ... | yes _ | no _ | no _ = ≡.refl

module Monad'+DecEq {M : Set m} {I : Set p}
  {raw : RawMonad' M I}
  (law : IsMonad' M I raw)
  (_≟_ : DecidableEquality I) where
  open RawMonad'+DecEq raw _≟_ public
  open IsMonad' law public
  open IfLemma
  open DecEqLemma _≟_

  open IsMonad'-consequences law

  at-ε : ∀ (i : I) → at ε i ≡ ε
  at-ε i =
    begin
      at ε i
    ≡⟨⟩
      ε • (λ j → if i == j then ε else ε)
    ≡⟨ •-cong₂ (λ _ → if-dud) ⟩
      ε • (λ j → ε)
    ≡⟨ ε-ε ⟩
      ε
    ∎
    where open ≡.≡-Reasoning

  at-ε• : ∀ (v : I → M) (i : I)  →
    at (ε • v) i ≡ at (v i) i
  at-ε• v i =
    begin
      at (ε • v) i
    ≡⟨⟩
      ε • α i (ε • v)
    ≡⟨⟩
      ε • (λ j → if i == j then ε • v else ε)
    ≡⟨ •-cong₂ (λ j → ≡.cong (if i == j then ε • v else_) (≡.sym ε-ε)) ⟩
      ε • (λ j → if i == j then ε • v else (ε • F.const ε))
    ≡⟨ •-cong₂ (λ j → case-apply₂ (i == j) (ε •_)) ⟨
      ε • (λ j → ε • (if i == j then v else F.const ε))
    ≡⟨ ε•-ε• (λ j → if i == j then _ else _) ⟩
      ε • (λ j → (if i == j then v else F.const ε) j)
    ≡⟨ •-cong₂ (λ j → case-apply₁ (i == j) _ _) ⟩
      ε • (λ j → if i == j then v j else ε)
    ≡⟨ •-cong₂ (λ j →
      rewrite-under-if i j (λ eq → ≡.cong v (≡.sym eq)))
    ⟩
      ε • (λ j → if i == j then v i else ε)
    ≡⟨⟩
      at (v i) i
    ∎
    where
      open ≡.≡-Reasoning
  
  at-at : ∀ (m : M) (i j : I) →
    at (at m i) j
      ≡
    (if (i == j) then (at m i) else ε)
  at-at m i j =
    begin
      at (at m i) j
    ≡⟨⟩
      at (ε • α i m) j
    ≡⟨ at-ε• (α i m) j ⟩
      at (α i m j) j
    ≡⟨ case-apply₂ (i == j) (λ m′ → at m′ j) ⟩
      (if (i == j) then at m j else at ε j)
    ≡⟨ rewrite-under-if i j (λ eq → ≡.cong (at m) (≡.sym eq)) ⟩
      (if (i == j) then at m i else at ε j)
    ≡⟨ ≡.cong (if (i == j) then at m i else_) (at-ε j) ⟩
      (if (i == j) then at m i else ε)
    ∎
    where
      open ≡.≡-Reasoning
  
  at-at-≡ : ∀ (m : M) (i : I) → at (at m i) i ≡ at m i
  at-at-≡ m i = ≡.trans (at-at m i i) (≡.cong (if_then at m i else ε) dec-refl)

  at-at-≢ : ∀ (m : M) {i j : I} (_ : i ≢ j) → at (at m i) j ≡ ε
  at-at-≢ m {i} {j} i≢j =
    ≡.trans (at-at m i j) (≡.cong (if_then at m i else ε) (dec-neq i≢j))
  
  -- to product of factors
  factorize : M → ((i : I) → FM i) 
  factorize m i = at m i , at-at-≡ m i

  -- from product of factors
  combine : ((i : I) → FM i) → M
  combine f = ε • λ i → proj₁ (f i)

  factorize-cong : F.Congruent _≡_ EqFactors factorize
  factorize-cong ≡.refl _ = ≡.refl

  combine-cong : F.Congruent EqFactors _≡_ combine
  combine-cong f≈g = •-cong₂ f≈g

  private
    isoʳ : ∀ (m : M) (f : Factors) → EqFactors f (factorize m) → combine f ≡ m
    isoʳ m f f≈ =
      begin
        combine f
      ≡⟨⟩
        (ε • λ i → proj₁ (f i))
      ≡⟨ •-cong₂ f≈ ⟩
        (ε • λ i → at m i)
      ≡⟨⟩
        (ε • λ i → ε • α i m)
      ≡⟨ ε•-ε• (λ i j → α i m j) ⟩
        (ε • λ i → α i m i)
      ≡⟨⟩
        (ε • λ i → if i == i then m else ε)
      ≡⟨ •-cong₂ (λ i → ≡.cong (if_then m else ε) dec-refl) ⟩
        (ε • λ i → m)
      ≡⟨ ε-• m ⟩
        m
      ∎
      where open ≡.≡-Reasoning
    
    isoˡ : ∀ (f : Factors) (m : M) → m ≡ combine f → EqFactors (factorize m) f
    isoˡ f _ ≡.refl j =
      begin
        proj₁ (factorize (combine f) j)
      ≡⟨⟩
        at (ε • f₁) j
      ≡⟨ at-ε• f₁ j ⟩
        at (f₁ j) j
      ≡⟨ proj₂ (f j) ⟩
        f₁ j
      ∎
      where
        f₁ : I → M
        f₁ i = proj₁ (f i)
        open ≡.≡-Reasoning
  
  factorize-combine-Inverse
    : F.Inverseᵇ _≡_ EqFactors factorize combine
  factorize-combine-Inverse = (λ {x y} → isoˡ x y) , (λ {x y} → isoʳ x y)

module _ {M : Set m} {I : Set p} (raw : RawMonad' M I) (_==_ : DecidableEquality I) where
  open RawMonad'+DecEq raw _==_
  
  toStateLike : ((I → M) → I → I) → RawStateLike M I
  toStateLike ql⁻¹ = record {
      ε = ε;
      _•_ = λ m v → m • (v F.∘′ σ m);
      t = λ i m → qr m (F.const ε) (σ⁻¹ m i)
    }
    where
      σ : M → I → I
      σ m = ql ε (at m)

      σ⁻¹ : M → I → I
      σ⁻¹ m = ql⁻¹ (at m) 
