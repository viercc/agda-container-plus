{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)

import Function as F
import Data.Product as Prod
open Prod using (Σ; ∃; _×_; proj₁; proj₂; _,_)

open import Data.Empty
open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_)
import Data.Bool.Properties as BoolProp

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Properties as NatProp
open import Data.Fin.Base
import Data.Fin.Properties as FinProp
open FinProp using (_≟_)

open import Relation.Binary
  using (IsEquivalence; Setoid; DecidableEquality)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≢_; _≗_)
open import Relation.Nullary
  using (¬_; contradiction; Dec; does; yes; no; ⌊_⌋; _→-dec_)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core
open import Container.Algebra.Monad.Monomial

-- Any Monomial monad on finite set of positions is isomorphic to
-- some StateLike. 
module Container.Algebra.Monad.Monomial.FinitePosition where

private
  infixr 8 _⨾_
  _⨾_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _⨾_ = ≡.trans

  witnessed-¬¬ : ∀ {a} {A : Set a}
    → Dec A → ¬ (¬ A) → A
  witnessed-¬¬ (yes witness) _ = witness
  witnessed-¬¬ (no ¬A) ¬¬A = ⊥-elim (¬¬A ¬A)

-- Facts about finite sets
module defs where
  private
    variable
      X Y : Set

  Surj : (X → Y) → Set
  Surj f = ∀ y → ∃ λ x → f x ≡ y

  Invˡ : (X → Y) → (Y → X) → Set
  Invˡ f g = ∀ x → g (f x) ≡ x

  Invʳ : (X → Y) → (Y → X) → Set
  Invʳ f g = ∀ y → f (g y) ≡ y

  Invᵇ : (X → Y) → (Y → X) → Set
  Invᵇ f g = Invʳ f g × Invˡ f g

  Inv-to-Inverse : {f : X → Y} {g : Y → X}
    → Invᵇ f g → F.Inverseᵇ _≡_ _≡_ f g
  Inv-to-Inverse {_} {_} {f} {g} (f-g , g-f) =
    (λ {x} eq → ≡.cong f eq ⨾ f-g x) ,
    (λ {x} eq → ≡.cong g eq ⨾ g-f x )

  Surj→Invʳ : {f : X → Y} → Surj f → ∃ (Invʳ f)
  Surj→Invʳ surj = (λ y → proj₁ (surj y)) , (λ y → proj₂ (surj y))

  Invʳ→Injective : (f : X → Y) (g : Y → X) → Invʳ f g → F.Injective _≡_ _≡_ g
  Invʳ→Injective f g fg-id {x₁} {x₂} gx₁≡gx₂ =
    begin
      x₁
    ≡⟨ fg-id x₁ ⟨
      f (g x₁)
    ≡⟨ ≡.cong f gx₁≡gx₂ ⟩
      f (g x₂)
    ≡⟨ fg-id x₂ ⟩
      x₂
    ∎
    where open ≡.≡-Reasoning

open defs

module Fin-lemmata where
  image? : ∀ {n : ℕ} (f : Fin n → Fin n) (y : Fin n)
    → Dec (∃ λ x → f x ≡ y)
  image? f y = FinProp.any? λ x → f x ≟ y

  Invʳ→¬¬Invˡ : ∀ {n : ℕ} (f g : Fin (ℕ.suc n) → Fin (ℕ.suc n))
    → Invʳ f g → ¬ (¬ Invˡ f g)
  Invʳ→¬¬Invˡ {n} f g fg-id ¬gf-id = NatProp.≤⇒≯ bad (NatProp.n<1+n n)
    where
      -- suppose x₀ be the one which fails
      --   Invˡ f g = (∀ x → g (f x) ≡ x)
      counterExample : ∃ λ x → g (f x) ≢ x
      counterExample =
        FinProp.¬∀⟶∃¬ _ _ (λ x → g (f x) ≟ x) ¬gf-id
      
      x₀ : Fin (ℕ.suc n)
      x₀ = proj₁ counterExample
      
      -- x₀ is not in the image of g
      x₀∉Img : ∀ y → x₀ ≢ g y
      x₀∉Img y x₀≡gy = proj₂ counterExample absurd
        where
          open ≡.≡-Reasoning
          absurd : g (f x₀) ≡ x₀
          absurd =
            begin
              g (f x₀)
            ≡⟨ ≡.cong (g F.∘ f) x₀≡gy ⟩
              g (f (g y))
            ≡⟨ ≡.cong g (fg-id y) ⟩
              g y
            ≡⟨ x₀≡gy ⟨
              x₀
            ∎
      
      -- let g′ be the new function made by punching out x₀
      -- from the codomain of g
      g′ : Fin (ℕ.suc n) → Fin n
      g′ y = punchOut (x₀∉Img y)

      -- g′ can be shown to be injective
      inj-g′ : F.Injective _≡_ _≡_ g′
      inj-g′ {x₁} {x₂} g′x₁≡g′x₂ = Invʳ→Injective f g fg-id gx₁≡gx₂
        where
          open ≡.≡-Reasoning

          gx₁≡gx₂ : g x₁ ≡ g x₂
          gx₁≡gx₂ =
            begin
              g x₁
            ≡⟨ FinProp.punchIn-punchOut (x₀∉Img x₁) ⟨
              punchIn x₀ (g′ x₁)
            ≡⟨ ≡.cong (punchIn x₀) g′x₁≡g′x₂ ⟩
              punchIn x₀ (g′ x₂)
            ≡⟨ FinProp.punchIn-punchOut (x₀∉Img x₂) ⟩
              g x₂
            ∎
      
      -- ... which means n + 1 ≤ n, contradiction.
      bad : ℕ.suc n ℕ.≤ n
      bad = FinProp.injective⇒≤ {f = g′} inj-g′

  -- If a function f from finite set Fin n to itself
  -- has a right inverse g, then g also is the left inverse of f.
  Invʳ→Invˡ : ∀ {n : ℕ} (f g : Fin n → Fin n)
    → Invʳ f g → Invˡ f g
  Invʳ→Invˡ {n = ℕ.zero} _ _ _ = λ ()
  Invʳ→Invˡ {n = ℕ.suc n} f g fg-id =
    witnessed-¬¬ (FinProp.all? λ x → g (f x) ≟ x) (Invʳ→¬¬Invˡ f g fg-id)


-- Given a Monomial monad on finite set I,
-- this monad necessarily satisfy LeftIso.
-- As shown in MonoDecEq, LeftIso property implies the existence of
-- StateLike isomorphic to the original Monomial monad.
module _ {ℓ} {M : Set ℓ} {n : ℕ}
  (let I = Fin n)
  {raw : RawMonad' M I} (law : IsMonad' M I raw) where
  
  import Container.Algebra.Monad.Monomial.DecidableEquality as MonoDecEq
  open MonoDecEq {M = M} {I = I} _≟_

  open RawMonad' raw
  open IsMonad' law
  open IsMonad'-consequences law
  open preliminary law

  open bool-lemmata
  open DecEq-lemmata

  -- lemma
  private
    e₁ : I → M
    e₁ = F.const ε

    Δ : (I → I → M) → I → M
    Δ w i = w i i

    d : (I → I → M) → I → M
    d w i = ε • w i

    diag-ee : ∀ (w : I → I → M) → diag ε e₁ w ≗ Δ w
    diag-ee w j = ≡.cong₂ w (ql-inner-ε _ _) (qr-outer-ε _ _)

    qr-ql-ee : ∀ (w : I → I → M) (j : I) →
      ql ε (Δ w) j ≡ ql ε (w (ql ε (d w) j)) (qr ε (d w) j)
    qr-ql-ee w j =
      begin
        ql ε (Δ w) j
      ≡⟨ ≡.cong (λ e → ql e _ _) ε-ε ⟨
        ql (ε • e₁) (Δ w) j
      ≡⟨ ql-cong₂ (diag-ee w) j ⟨
        ql (ε • e₁) (diag ε e₁ w) j
      ≡⟨ qr-outer-ε ε _ ⟨
        qr ε e₁ (ql (ε • e₁) (diag ε e₁ w) j)
      ≡⟨ qr-ql ε e₁ w j ⟩
        ql ε (w (ql ε (d w) j)) (qr ε (d w) j)
      ∎
      where open ≡.≡-Reasoning
    
    qr-qr-ee : ∀ (w : I → I → M) (j : I) →
      qr ε (Δ w) j ≡ qr ε (w (ql ε (d w) j)) (qr ε (d w) j)
    qr-qr-ee w j =
      begin
        qr ε (Δ w) j
      ≡⟨ ≡.cong (λ e → qr e _ _) ε-ε ⟨
        qr (ε • e₁) (Δ w) j
      ≡⟨ qr-cong₂ (diag-ee w) j ⟨
        qr (ε • e₁) (diag ε e₁ w) j
      ≡⟨ qr-qr ε e₁ w j ⟩
        qr ε (w (ql ε (d w) j)) (qr ε (d w) j)
      ∎
      where open ≡.≡-Reasoning
    
  -- single-position case:
  --   `ql ε (α i mᵢ) : I → I`
  --      (which we well call `r` for short)
  -- has an inverse function of it (i.e. is a permutation.)
  module single-position (i : I) (m : M) where
    mᵢ : M
    mᵢ = m at i

    r s r̂ ŝ : I → I
    r = ql ε (α i mᵢ)
    s = qr ε (α i mᵢ)
    r̂ = ql ε (β i mᵢ)
    ŝ = qr ε (β i mᵢ)

    r̂≗id : r̂ ≗ F.id
    r̂≗id j =
      begin
        ql ε (β i mᵢ) j
      ≡⟨ ql-ε-at (β i mᵢ) j ⟨
        ql ε ((ε • β i mᵢ) at_) j
      ≡⟨ ql-cong₂ (λ k → ≡.cong (_at k) (ε•β-at m i) ⨾ at-ε k) j ⟩
        ql ε (λ k → ε) j
      ≡⟨ ql-inner-ε ε j ⟩
        j
      ∎
      where open ≡.≡-Reasoning
    
    w₁ : I → I → M
    w₁ j = if i == j then e₁ else α i mᵢ

    Δw₁≗e₁ : Δ w₁ ≗ e₁
    Δw₁≗e₁ j =
      begin
        Δ w₁ j
      ≡⟨⟩
        (if i == j then e₁ else α i mᵢ) j
      ≡⟨ case-apply₁ (i == j) _ _ ⟩
        (if i == j then ε else α i mᵢ j)
      ≡⟨ if-else-if (i == j) ⟩
        (if i == j then ε else ε)
      ≡⟨ if-dud ⟩
        ε
      ∎
      where open ≡.≡-Reasoning

    dw₁≗βmᵢ : d w₁ ≗ β i mᵢ
    dw₁≗βmᵢ j =
      begin
        d w₁ j
      ≡⟨⟩
        (ε • (if i == j then e₁ else α i mᵢ))
      ≡⟨ case-apply₂ (i == j) (ε •_) ⟩
        (if i == j then ε • e₁ else ε • α i mᵢ)
      ≡⟨ ≡.cong₂ (if i == j then_else_) ε-ε (at-at-≡ m i) ⟩
        (if i == j then ε else mᵢ)
      ≡⟨⟩
        β i mᵢ j
      ∎
      where open ≡.≡-Reasoning

    ql-dw₁≗id : ql ε (d w₁) ≗ F.id
    ql-dw₁≗id j = ql-cong₂ dw₁≗βmᵢ j ⨾ r̂≗id j

    qr-dw₁≗ŝ : qr ε (d w₁) ≗ ŝ
    qr-dw₁≗ŝ = qr-cong₂ dw₁≗βmᵢ 

    ŝi≡i : ŝ i ≡ i
    ŝi≡i = begin
        ŝ i
      ≡⟨ ql-inner-ε ε (ŝ i) ⟨
        ql ε e₁ (ŝ i)
      ≡⟨ ≡.cong (λ v → ql ε v (ŝ i)) w₁i≡e₁ ⟨
        ql ε (w₁ i) (ŝ i)
      ≡⟨ ≡.cong₂ (λ j' k' → ql ε (w₁ j') k') (ql-dw₁≗id i) (qr-dw₁≗ŝ i) ⟨
        ql ε (w₁ (ql ε (d w₁) i)) (qr ε (d w₁) i)
      ≡⟨ qr-ql-ee w₁ i ⟨
        ql ε (Δ w₁) i
      ≡⟨ ql-cong₂ Δw₁≗e₁ i ⟩
        ql ε e₁ i
      ≡⟨ ql-inner-ε ε i ⟩
        i
      ∎
      where
        w₁i≡e₁ : w₁ i ≡ e₁
        w₁i≡e₁ = ≡.cong (if_then e₁ else α i mᵢ) (dec-refl {i = i})

        open ≡.≡-Reasoning

    rŝ-id-i≢j : ∀ j → i ≢ j → r (ŝ j) ≡ j
    rŝ-id-i≢j j i≢j = ≡.sym eq
      where
        open ≡.≡-Reasoning

        w₁j≡αmᵢ : w₁ j ≡ α i mᵢ
        w₁j≡αmᵢ = ≡.cong (if_then e₁ else α i mᵢ) (dec-neq i≢j)

        eq : j ≡ r (ŝ j)
        eq = begin
            j
          ≡⟨ ql-inner-ε ε j ⟨
            ql ε e₁ j
          ≡⟨ ql-cong₂ Δw₁≗e₁ j ⟨
            ql ε (Δ w₁) j
          ≡⟨ qr-ql-ee w₁ j ⟩
            ql ε (w₁ (ql ε (d w₁) j)) (qr ε (d w₁) j)
          ≡⟨ ≡.cong₂ (λ j' k' → ql ε (w₁ j') k') (ql-dw₁≗id j) (qr-dw₁≗ŝ j) ⟩
            ql ε (w₁ j) (ŝ j)
          ≡⟨ ≡.cong (λ v → ql ε v (ŝ j)) w₁j≡αmᵢ ⟩
            ql ε (α i mᵢ) (ŝ j)
          ≡⟨⟩
            r (ŝ j)
          ∎

    -- There is a preimage r⁻¹(i) or there isn't any.
    r⁻¹-i-or-not : Dec (∃ λ k → r k ≡ i)
    r⁻¹-i-or-not = FinProp.any? (λ k → r k ≟ i)

    -- When it exists, we can construct the inverse of r.
    module exist-case (proof : ∃ λ k → r k ≡ i) where
      k₀ : I
      k₀ = proj₁ proof

      rk₀≡i : r k₀ ≡ i
      rk₀≡i = proj₂ proof

      s′ : I → I
      s′ j = if i == j then k₀ else ŝ j

      Invʳ-s′ : Invʳ r s′
      Invʳ-s′ j = begin
          r (s′ j)
        ≡⟨⟩
          r (if i == j then k₀ else ŝ j)
        ≡⟨ case-apply₂ (i == j) r ⟩
          (if (i == j) then r k₀ else r (ŝ j))
        ≡⟨ rewrite-under-if-else i j
              (λ i≡j → rk₀≡i ⨾ i≡j)
              (λ i≢j → rŝ-id-i≢j j i≢j) ⟩
          (if (i == j) then j else j)
        ≡⟨ if-dud ⟩
          j
        ∎ 
        where open ≡.≡-Reasoning
      
      Invˡ-s′ : Invˡ r s′
      Invˡ-s′ = Fin-lemmata.Invʳ→Invˡ r s′ Invʳ-s′

      there-is-inverse : ∃ λ r⁻¹ → Invᵇ r r⁻¹
      there-is-inverse = s′ , (Invʳ-s′ , Invˡ-s′)
    
    -- Assuming non-existence leads contradicion.
    module not-exist-case (disproof : ¬ (∃ λ k → r k ≡ i)) where
      i≢rk : ∀ k → i ≢ r k
      i≢rk k hyp = disproof (k , ≡.sym hyp)

      w₂ : I → I → M
      w₂ j = if i == j then α i mᵢ else e₁

      Δw₂≗αmᵢ : Δ w₂ ≗ α i mᵢ
      Δw₂≗αmᵢ j =
        begin
          Δ w₂ j
        ≡⟨ case-apply₁ (i == j) _ _ ⟩
          (if i == j then α i mᵢ j else ε)
        ≡⟨ if-then-if (i == j) ⟩
          (if i == j then mᵢ else ε)
        ≡⟨⟩
          α i mᵢ j
        ∎
        where open ≡.≡-Reasoning
      
      dw₂≗αmᵢ : d w₂ ≗ α i mᵢ
      dw₂≗αmᵢ j =
        begin
          d w₂ j
        ≡⟨⟩
          ε • (if i == j then α i mᵢ else e₁)
        ≡⟨ case-apply₂ (i == j) (ε •_) ⟩
          (if i == j then ε • α i mᵢ else ε • e₁)
        ≡⟨ ≡.cong₂ (if i == j then_else_) (at-at-≡ m i) ε-ε ⟩
          (if i == j then mᵢ else ε)
        ≡⟨⟩
          α i mᵢ j
        ∎
        where open ≡.≡-Reasoning

      ql-dw₂≗r : ql ε (d w₂) ≗ r
      ql-dw₂≗r = ql-cong₂ dw₂≗αmᵢ

      qr-dw₂≗s : qr ε (d w₂) ≗ s
      qr-dw₂≗s = qr-cong₂ dw₂≗αmᵢ

      w₂-rj≡e₁ : ∀ j → w₂ (r j) ≡ e₁
      w₂-rj≡e₁ j = ≡.cong (if_then _ else e₁) (dec-neq (i≢rk j))

      r≗s : r ≗ s
      r≗s j =
        begin
          r j
        ≡⟨⟩
          ql ε (α i mᵢ) j
        ≡⟨ ql-cong₂ (λ k → Δw₂≗αmᵢ k) j ⟨
          ql ε (Δ w₂) j
        ≡⟨ qr-ql-ee w₂ j ⟩
          ql ε (w₂ (ql ε (d w₂) j)) (qr ε (d w₂) j)
        ≡⟨ ≡.cong₂ (λ j' k' → ql ε (w₂ j') k') (ql-dw₂≗r j) (qr-dw₂≗s j) ⟩
          ql ε (w₂ (r j)) (s j)
        ≡⟨ ≡.cong (λ v → ql ε v (s j)) (w₂-rj≡e₁ j) ⟩
          ql ε e₁ (s j)
        ≡⟨ ql-inner-ε ε (s j) ⟩
          s j
        ∎
        where open ≡.≡-Reasoning
      
      w₃ : I → I → M
      w₃ j = if i == j then α i mᵢ else β i mᵢ

      Δw₃≗const-mᵢ : Δ w₃ ≗ F.const mᵢ
      Δw₃≗const-mᵢ j =
        begin
          Δ w₃ j
        ≡⟨ case-apply₁ (i == j) _ _ ⟩
          (if i == j then α i mᵢ j else β i mᵢ j)
        ≡⟨ rewrite-under-if-else i j
              (λ i≡j → ≡.cong (if_then mᵢ else ε) (dec-eq i≡j))
              (λ i≢j → ≡.cong (if_then ε else mᵢ) (dec-neq i≢j)) ⟩
          (if i == j then mᵢ else mᵢ)
        ≡⟨ if-dud ⟩
          mᵢ
        ∎
        where open ≡.≡-Reasoning
      
      dw₃≗αmᵢ : d w₃ ≗ α i mᵢ
      dw₃≗αmᵢ j =
        begin
          d w₃ j
        ≡⟨ case-apply₂ (i == j) (ε •_) ⟩
          (if i == j then ε • α i mᵢ else ε • β i mᵢ)
        ≡⟨ ≡.cong₂ (if i == j then_else_) (at-at-≡ m i) (ε•β-at m i) ⟩
          (if i == j then mᵢ else ε)
        ≡⟨⟩
          α i mᵢ j
        ∎
        where open ≡.≡-Reasoning
      
      ql-dw₃≗r : ql ε (d w₃) ≗ r
      ql-dw₃≗r = ql-cong₂ dw₃≗αmᵢ

      qr-dw₃≗s : qr ε (d w₃) ≗ s
      qr-dw₃≗s = qr-cong₂ dw₃≗αmᵢ

      ŝ-s-id : ∀ j → j ≡ ŝ (s j)
      ŝ-s-id j =
        begin
          j
        ≡⟨ qr-outer-ε mᵢ j ⟨
          qr ε (F.const mᵢ) j
        ≡⟨ qr-cong₂ Δw₃≗const-mᵢ j ⟨
          qr ε (Δ w₃) j
        ≡⟨ qr-qr-ee w₃ j ⟩
          qr ε (w₃ (ql ε (d w₃) j)) (qr ε (d w₃) j)
        ≡⟨ ≡.cong₂ (λ j' k' → qr ε (w₃ j') k') (ql-dw₃≗r j) (qr-dw₃≗s j) ⟩
          qr ε (w₃ (r j)) (s j)
        ≡⟨ ≡.cong (λ v → qr ε v (s j)) w₃rj≡βmᵢ ⟩
          qr ε (β i mᵢ) (s j)
        ≡⟨⟩
          ŝ (s j)
        ∎
        where
          open ≡.≡-Reasoning
          w₃rj≡βmᵢ : w₃ (r j) ≡ β i mᵢ
          w₃rj≡βmᵢ = ≡.cong (if_then _ else β i mᵢ) (dec-neq (i≢rk j))

      -- s is a right inverse of ŝ 
      Invʳ-ŝ-s : Invʳ ŝ s
      Invʳ-ŝ-s j = ≡.sym (ŝ-s-id j) 

      -- ... which then implies s is the inverse of ŝ
      Invˡ-ŝ-s : Invˡ ŝ s
      Invˡ-ŝ-s = Fin-lemmata.Invʳ→Invˡ ŝ s Invʳ-ŝ-s

      -- ... which then implies r = s is surjective,
      -- and in fact there's k s.t. i≡rk
      i≡rŝi : i ≡ r (ŝ i)
      i≡rŝi =
        begin
          i
        ≡⟨ Invˡ-ŝ-s i ⟨
          s (ŝ i)
        ≡⟨ r≗s (ŝ i) ⟨
          r (ŝ i)
        ∎
        where open ≡.≡-Reasoning

      -- ... which contradicts to the hypothesis.
      bad : ⊥
      bad = i≢rk (ŝ i) i≡rŝi
    
    -- Therefore, the inverse of r always exists.
    r-inverse : ∃ λ r⁻¹ → Invᵇ r r⁻¹
    r-inverse with r⁻¹-i-or-not
    ... | yes proof    = exist-case.there-is-inverse proof
    ... | no  disproof = ⊥-elim (not-exist-case.bad disproof)
    
  -- Use single-position case to show generic case
  module ql-inv-construct (v : I → M) where
    -- we're to show `ql ε v : I → I` has inverse.
    m : M
    m = ε • v

    -- But its sufficient to show only for `h = ql ε (m at_)`.
    h : I → I
    h = ql ε (m at_)

    ql-v≗ql-mi : ql ε v ≗ h
    ql-v≗ql-mi j = ≡.sym (ql-ε-at v j)

    -- definitions
    σ : I → I → I
    σ i = ql ε (α i (m at i))

    σ-has-inv : ∀ i → ∃ λ f → Invᵇ (σ i) f
    σ-has-inv i = single-position.r-inverse i m

    σ⁻¹ : I → I → I
    σ⁻¹ i = proj₁ (σ-has-inv i)

    σ-σ⁻¹ : ∀ i j → σ i (σ⁻¹ i j) ≡ j
    σ-σ⁻¹ i = proj₁ (proj₂ (σ-has-inv i))

    σ⁻¹-σ : ∀ i j → σ⁻¹ i (σ i j) ≡ j
    σ⁻¹-σ i = proj₂ (proj₂ (σ-has-inv i))
    
    -- This g is the inverse of h
    g : I → I
    g k = qr ε (α k m) (σ⁻¹ k k)
  
    w₄ : I → I → M
    w₄ i = α i (m at i)

    Δw₄≗mᵢ : Δ w₄ ≗ (m at_)
    Δw₄≗mᵢ j = ≡.cong (if_then m at j else ε) (dec-refl {i = j})

    dw₄≗mᵢ : d w₄ ≗ (m at_)
    dw₄≗mᵢ j = at-at-≡ m j

    h-as-σqr : ∀ j → h j ≡ σ (h j) (qr ε (m at_) j)
    h-as-σqr j =
      begin
        h j
      ≡⟨ ql-cong₂ Δw₄≗mᵢ j ⟨
        ql ε (Δ w₄) j
      ≡⟨ qr-ql-ee w₄ j ⟩
        ql ε (w₄ (ql ε (d w₄) j)) (qr ε (d w₄) j)
      ≡⟨ ≡.cong₂ (λ j' k' → ql ε (w₄ j') k')
          (ql-cong₂ dw₄≗mᵢ j)
          (qr-cong₂ dw₄≗mᵢ j) ⟩
        ql ε (w₄ (h j)) (qr ε (m at_) j)
      ≡⟨⟩
        σ (h j) (qr ε (m at_) j)
      ∎
      where open ≡.≡-Reasoning
    
    qr-as-σ⁻¹h : ∀ j → qr ε (m at_) j ≡ σ⁻¹ (h j) (h j)
    qr-as-σ⁻¹h j =
      begin
        qr ε (m at_) j
      ≡⟨ σ⁻¹-σ (h j) (qr ε (m at_) j) ⟨
        σ⁻¹ (h j) (σ (h j) (qr ε (m at_) j))
      ≡⟨ ≡.cong (σ⁻¹ (h j)) (h-as-σqr j) ⟨
        σ⁻¹ (h j) (h j)
      ∎
      where open ≡.≡-Reasoning
    
    w₅ : I → I → M
    w₅ i = α i m

    Δw₅≗const-m : Δ w₅ ≗ F.const m
    Δw₅≗const-m j = ≡.cong (if_then _ else _) (dec-refl {i = j})

    _ : d w₅ ≡ (m at_)
    _ = ≡.refl

    g-h-id' : ∀ j → j ≡ g (h j)
    g-h-id' j =
      begin
        j
      ≡⟨ qr-outer-ε m j ⟨
        qr ε (F.const m) j
      ≡⟨ qr-cong₂ Δw₅≗const-m j ⟨
        qr ε (Δ w₅) j
      ≡⟨ qr-qr-ee w₅ j ⟩
        qr ε (w₅ (ql ε (d w₅) j)) (qr ε (d w₅) j)
      ≡⟨⟩
        qr ε (w₅ (h j)) (qr ε (m at_) j)
      ≡⟨ ≡.cong (qr ε (w₅ (h j))) (qr-as-σ⁻¹h j) ⟩
        qr ε (α (h j) m) (σ⁻¹ (h j) (h j))
      ≡⟨⟩
        g (h j)
      ∎
      where open ≡.≡-Reasoning
    
    g-ql-id : Invʳ g (ql ε v)
    g-ql-id j =
      begin
        g (ql ε v j)
      ≡⟨ ≡.cong g (ql-v≗ql-mi j) ⟩
        g (h j)
      ≡⟨ g-h-id' j ⟨
        j
      ∎
      where open ≡.≡-Reasoning

    ql-g-id : Invˡ g (ql ε v)
    ql-g-id = Fin-lemmata.Invʳ→Invˡ g (ql ε v) g-ql-id

    -- g is the inverse of (ql ε v)
    ql-inv-correct : F.Inverseᵇ _≡_ _≡_ (ql ε v) g
    ql-inv-correct = Inv-to-Inverse (ql-g-id , g-ql-id)

  goal : LeftIso raw
  goal = record {
      ql⁻¹ = ql-inv-construct.g;
      ql⁻¹-correct = ql-inv-construct.ql-inv-correct
    }