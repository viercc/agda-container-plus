{-# OPTIONS --without-K --safe #-}

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
  
  infixr 8 _⨾_
  _⨾_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _⨾_ = ≡.trans

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

  -- A condition on Monomial monad which implies
  -- it actually defines StateLike
  LeftTrivial : RawMonad' M I → Set (m ⊔ p)
  LeftTrivial raw' = ∀ m v i → ql m v i ≡ i
    where ql = RawMonad'.ql raw'

  -- StateLike implies Monad' /\ LeftTrivial
  module toMonomial (rawSL : RawStateLike M I) where
    open RawStateLike rawSL
    
    raw' : RawMonad' M I
    raw' = record {
        ε = ε;
        _•_ = _•_;
        ql = λ _ _ i → i;
        qr = λ m _ i → t i m
      }
    
    ql-id : LeftTrivial raw'
    ql-id = λ m v i → ≡.refl

    toIsMonad' : IsStateLike M I rawSL → IsMonad' M I raw'
    toIsMonad' isSL = record {
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
        open IsStateLike isSL

  -- Monad' /\ LeftTrivial implies StateLike
  module fromMonomial (raw' : RawMonad' M I) (ql-id : LeftTrivial raw') where
    open RawMonad' raw'
    
    private
      e₁ : I → M
      e₁ _ = ε 

      e₂ : I → I → M
      e₂ _ _ = ε

      -- Definition of rawStateLike
      t : I → M → I
      t i m = qr m e₁ i

      diag : M → (I → I → M) → (I → M)
      diag m w i = w i (t i m)

      zip : (I → M) → (I → I → M) → (I → M)
      zip v w i = v i • w i

    rawSL : RawStateLike M I
    rawSL = record {
        ε = ε;
        _•_ = _•_;
        t = t
      }
    
    module _ (law' : IsMonad' M I raw') where
      open IsMonad' law' hiding (zip)

      qr-v-irrelevant : ∀ m v i → t i m ≡ qr m v i
      qr-v-irrelevant m v i =
        begin
          t i m
        ≡⟨⟩
          qr m e₁ i
        ≡⟨ ≡.cong (qr m e₁) (ql-id _ _ i) ⟨
          qr m e₁ (ql _ _ i)
        ≡⟨ qr-ql m e₁ (λ j _ → v j) i ⟩
          ql _ _ (qr m u i)
        ≡⟨ ql-id _ _ (qr m u i) ⟩
          qr m u i
        ≡⟨ qr-cong₂ u≗v i ⟩
          qr m v i
        ∎
        where
          u : I → M
          u = zip e₁ (λ j _ → v j)

          u≗v : (i : I) → u i ≡ v i
          u≗v i = ε-• (v i)
          
          open ≡.≡-Reasoning

    private
      module lawImpl (law' : IsMonad' M I raw') where
        module M = IsMonad' law'
        open M using (•-cong₂; •-ε; ε-•) public
        
        diag-equiv : (m : M) (v : I → M) (w : I → I → M) → diag m w ≗ M.diag m v w
        diag-equiv m v w i =
          begin
            diag m w i
          ≡⟨⟩
            w i (t i m)
          ≡⟨ ≡.cong₂ w (≡.sym (ql-id m v i)) (qr-v-irrelevant law' m v i) ⟩
            w (ql m v i) (qr m v i)
          ≡⟨⟩
            M.diag m v w i
          ∎
          where
            open ≡.≡-Reasoning

        •-• : ∀ (m : M) (v : I → M) (w : I → I → M)
          → (m • v) • diag m w ≡ m • zip v w
        •-• m v w = •-cong₂ (diag-equiv m v w) ⨾ M.•-• m v w

        t-ε : ∀ (i : I) → t i ε ≡ i
        t-ε = M.qr-outer-ε ε

        t-• : ∀ (m : M) (v : I → M)
          → (i : I)
          → t i (m • v) ≡ t (t i m) (v i)
        t-• m v i =
          begin
            t i (m • v)
          ≡⟨⟩
            qr (m • v) e₁ i
          ≡⟨⟩
            qr (m • v) (M.diag m v e₂) i
          ≡⟨ M.qr-qr m v e₂ i ⟩
            qr (v (ql m _ i)) e₁ (qr m _ i)
          ≡⟨ ≡.cong₂ (λ j k → qr (v j) e₁ k)
              (ql-id _ _ i)
              (≡.sym (qr-v-irrelevant law' m _ i)) ⟩
            qr (v i) e₁ (t i m)
          ≡⟨⟩
            t (t i m) (v i)
          ∎
          where open ≡.≡-Reasoning

    fromIsMonad' : IsMonad' M I raw' → IsStateLike M I rawSL
    fromIsMonad' law' = record { lawImpl law' }

