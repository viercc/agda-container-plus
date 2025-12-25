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

open import Container.Algebra.Monad.Monomial

-- Any Monomial monad on finite set of positions is isomorphic to
-- some StateLike. 
module Container.Algebra.Monad.Monomial.FinitePosition where

private
  infixr 8 _⨾_
  _⨾_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _⨾_ = ≡.trans

-- Facts about finite sets
module defs where
  private
    variable
      X Y : Set

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
  -- EITHER (P x) holds for all (x : A) OR
  -- there's a counterexample x₀ such that ¬ P x₀.
  data Searched {a b} {A : Set a} (P : A → Set b) : Set (a ⊔ b) where
    all-yes : (∀ x → P x) → Searched P
    counter : (∃ λ x → ¬ P x) → Searched P
  
  -- Searched is stronger than Dec (∀ P)
  Searched→Dec∀ : ∀ {a b} {A : Set a} {P : A → Set b}
    → Searched P → Dec (∀ x → P x)
  Searched→Dec∀ (all-yes allP) = yes allP
  Searched→Dec∀ (counter (x , ¬Px)) = no (λ allP → ¬Px (allP x))

  -- Searched is stronger than Dec (∃ ¬P)
  Searched→Dec¬P : ∀ {a b} {A : Set a} {P : A → Set b}
    → Searched P → Dec (∃ λ x → ¬ P x)
  Searched→Dec¬P (all-yes allP) = no (λ (x , ¬Px) → ¬Px (allP x))
  Searched→Dec¬P (counter counterexample) = yes counterexample

  cons-search : ∀ {b} {n : ℕ} {P : Fin (ℕ.suc n) → Set b}
    → P zero → Searched (P F.∘ suc) → Searched P
  cons-search P0 (all-yes Pn) = all-yes (FinProp.∀-cons P0 Pn)
  cons-search _  (counter (x , disproof)) = counter (suc x , disproof)

  -- Finite sets can be searched with decidable predicate.
  search? : ∀ {b} {n : ℕ} {P : Fin n → Set b}
    → (∀ x → Dec (P x)) → Searched P
  search? {_} {ℕ.zero}   _  = all-yes (λ ())
  search? {_} {ℕ.suc n′} P? with P? zero
  ... | yes P0 = cons-search P0 (search? (P? F.∘ suc))
  ... | no ¬P0 = counter (zero , ¬P0)

  private
    -- To prove Invʳ→Invˡ, first prove a slightly weaker
    -- Invʳ → "there must not exist a counterexample to Invˡ"
    Invʳ→noCounterexample : ∀ {n : ℕ} (f g : Fin n → Fin n)
      → Invʳ f g → ¬ (∃ λ x → g (f x) ≢ x)
    Invʳ→noCounterexample {ℕ.zero}  _ _ _ = λ ()
    Invʳ→noCounterexample {ℕ.suc n} f g fg-id (x₀ , gfx₀≢x₀)
        = NatProp.≤⇒≯ bad (NatProp.n<1+n n)
      where
        -- Given a counterexample x₀ to
        --  ∀ x → g (f x) ≡ x,
        -- prove a contradiction.

        -- x₀ is not in the image of g
        x₀∉Img : ∀ y → x₀ ≢ g y
        x₀∉Img y x₀≡gy = gfx₀≢x₀ wrong
          where
            open ≡.≡-Reasoning
            wrong : g (f x₀) ≡ x₀
            wrong =
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

        -- Equality through g′ → equality through g
        g′≡→g≡ : ∀ {x₁ x₂} → g′ x₁ ≡ g′ x₂ → g x₁ ≡ g x₂
        g′≡→g≡ {x₁} {x₂} g′x₁≡g′x₂ =
          begin
            g x₁
          ≡⟨ FinProp.punchIn-punchOut (x₀∉Img x₁) ⟨
            punchIn x₀ (g′ x₁)
          ≡⟨ ≡.cong (punchIn x₀) g′x₁≡g′x₂ ⟩
            punchIn x₀ (g′ x₂)
          ≡⟨ FinProp.punchIn-punchOut (x₀∉Img x₂) ⟩
            g x₂
          ∎
          where
            open ≡.≡-Reasoning

        -- g′ inherits injectivity from g
        inj-g′ : F.Injective _≡_ _≡_ g′
        inj-g′ = Invʳ→Injective f g fg-id F.∘ g′≡→g≡
        
        -- ... which means n + 1 ≤ n, contradiction.
        bad : ℕ.suc n ℕ.≤ n
        bad = FinProp.injective⇒≤ {f = g′} inj-g′

  -- If an endo-function `f : Fin n → Fin n`
  -- has a right inverse `g`, then `g` also is the left inverse of `f`.
  Invʳ→Invˡ : ∀ {n : ℕ} (f g : Fin n → Fin n)
    → Invʳ f g → Invˡ f g
  Invʳ→Invˡ f g fg-id with search? (λ x → g (f x) ≟ x)
  ... | all-yes gf-id = gf-id
  ... | counter cex = contradiction cex (Invʳ→noCounterexample f g fg-id)

  -- Therefore, such `(f , g)` are inverses.
  Invʳ→Invᵇ : ∀ {n : ℕ} (f g : Fin n → Fin n)
    → Invʳ f g → Invᵇ f g
  Invʳ→Invᵇ f g fg-id = fg-id , Invʳ→Invˡ f g fg-id

  -- The proof is self-dual.
  Invˡ→Invᵇ : ∀ {n : ℕ} (f g : Fin n → Fin n)
    → Invˡ f g → Invᵇ f g
  Invˡ→Invᵇ f g gf-id = Invʳ→Invˡ g f gf-id , gf-id

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
    
  -- single-position case:
  --   `α = ql ε (at i mᵢ) : I → I`
  -- has its inverse `α⁻¹`.
  module single-position (i : I) (m : M) where
    mᵢ : M
    mᵢ = proj i m

    α αᵣ β βᵣ : I → I
    α = ql ε (at i mᵢ)
    αᵣ = qr ε (at i mᵢ)
    β = ql ε (but i mᵢ)
    βᵣ = qr ε (but i mᵢ)
    
    β≗id : β ≗ F.id
    β≗id j =
      begin
        ql ε (but i mᵢ) j
      ≡⟨ ql-ε-proj j (but i mᵢ) ⟨
        ql ε (λ k → proj k (ε • but i mᵢ)) j
      ≡⟨ ql-cong₂ (λ k → ≡.cong (proj k) (ε•but-proj m i) ⨾ proj-ε k) j ⟩
        ql ε (λ k → ε) j
      ≡⟨ ql-inner-ε ε j ⟩
        j
      ∎
      where open ≡.≡-Reasoning
    
    w₁ : I → I → M
    w₁ j = if i == j then e₁ else at i mᵢ

    Δw₁≗e₁ : Δ w₁ ≗ e₁
    Δw₁≗e₁ j =
      begin
        Δ w₁ j
      ≡⟨⟩
        (if i == j then e₁ else at i mᵢ) j
      ≡⟨ case-apply₁ (i == j) _ _ ⟩
        (if i == j then ε else at i mᵢ j)
      ≡⟨ if-else-if (i == j) ⟩
        (if i == j then ε else ε)
      ≡⟨ if-dud ⟩
        ε
      ∎
      where open ≡.≡-Reasoning

    dw₁≗but : d w₁ ≗ but i mᵢ
    dw₁≗but j =
      begin
        d w₁ j
      ≡⟨⟩
        (ε • (if i == j then e₁ else at i mᵢ))
      ≡⟨ case-apply₂ (i == j) (ε •_) ⟩
        (if i == j then ε • e₁ else ε • at i mᵢ)
      ≡⟨ ≡.cong₂ (if i == j then_else_) ε-ε (proj-proj-≡ i m) ⟩
        (if i == j then ε else mᵢ)
      ≡⟨⟩
        but i mᵢ j
      ∎
      where open ≡.≡-Reasoning

    ql-dw₁≗id : ql ε (d w₁) ≗ F.id
    ql-dw₁≗id j = ql-cong₂ dw₁≗but j ⨾ β≗id j

    qr-dw₁≗βᵣ : qr ε (d w₁) ≗ βᵣ
    qr-dw₁≗βᵣ = qr-cong₂ dw₁≗but

    αβᵣ-id-i≢j : ∀ j → i ≢ j → α (βᵣ j) ≡ j
    αβᵣ-id-i≢j j i≢j = ≡.sym eq
      where
        open ≡.≡-Reasoning

        w₁j≡at : w₁ j ≡ at i mᵢ
        w₁j≡at = ≡.cong (if_then e₁ else at i mᵢ) (dec-neq i≢j)

        eq : j ≡ α (βᵣ j)
        eq = begin
            j
          ≡⟨ ql-inner-ε ε j ⟨
            ql ε e₁ j
          ≡⟨ ql-cong₂ Δw₁≗e₁ j ⟨
            ql ε (Δ w₁) j
          ≡⟨ qr-ql-ee w₁ j ⟩
            ql ε (w₁ (ql ε (d w₁) j)) (qr ε (d w₁) j)
          ≡⟨ ≡.cong₂ (λ j' k' → ql ε (w₁ j') k') (ql-dw₁≗id j) (qr-dw₁≗βᵣ j) ⟩
            ql ε (w₁ j) (βᵣ j)
          ≡⟨ ≡.cong (λ v → ql ε v (βᵣ j)) w₁j≡at ⟩
            ql ε (at i mᵢ) (βᵣ j)
          ≡⟨⟩
            α (βᵣ j)
          ∎

    -- There is a preimage α⁻¹(i) or there isn't any.
    α⁻¹i-or-not : Dec (∃ λ k → α k ≡ i)
    α⁻¹i-or-not = FinProp.any? (λ k → α k ≟ i)

    -- When it exists, we can construct the inverse of α.
    module exist-case (proof : ∃ λ k → α k ≡ i) where
      k₀ : I
      k₀ = proj₁ proof

      αk₀≡i : α k₀ ≡ i
      αk₀≡i = proj₂ proof

      α⁻¹ : I → I
      α⁻¹ j = if i == j then k₀ else βᵣ j

      Invʳ-α : Invʳ α α⁻¹
      Invʳ-α j = begin
          α (α⁻¹ j)
        ≡⟨⟩
          α (if i == j then k₀ else βᵣ j)
        ≡⟨ case-apply₂ (i == j) α ⟩
          (if (i == j) then α k₀ else α (βᵣ j))
        ≡⟨ rewrite-under-if-else i j
              (λ i≡j → αk₀≡i ⨾ i≡j)
              (λ i≢j → αβᵣ-id-i≢j j i≢j) ⟩
          (if i == j then j else j)
        ≡⟨ if-dud ⟩
          j
        ∎ 
        where open ≡.≡-Reasoning
      
      there-is-α⁻¹ : ∃ λ γ → Invᵇ α γ
      there-is-α⁻¹ = α⁻¹ , (Fin-lemmata.Invʳ→Invᵇ α α⁻¹ Invʳ-α)
    
    -- Assuming non-existence leads contradicion.
    module not-exist-case (disproof : ¬ (∃ λ k → α k ≡ i)) where
      i≢αk : ∀ k → i ≢ α k
      i≢αk k hyp = disproof (k , ≡.sym hyp)

      w₂ : I → I → M
      w₂ j = if i == j then at i mᵢ else e₁

      Δw₂≗at : Δ w₂ ≗ at i mᵢ
      Δw₂≗at j =
        begin
          Δ w₂ j
        ≡⟨ case-apply₁ (i == j) _ _ ⟩
          (if i == j then at i mᵢ j else ε)
        ≡⟨ if-then-if (i == j) ⟩
          (if i == j then mᵢ else ε)
        ≡⟨⟩
          at i mᵢ j
        ∎
        where open ≡.≡-Reasoning
      
      dw₂≗at : d w₂ ≗ at i mᵢ
      dw₂≗at j =
        begin
          d w₂ j
        ≡⟨⟩
          ε • (if i == j then at i mᵢ else e₁)
        ≡⟨ case-apply₂ (i == j) (ε •_) ⟩
          (if i == j then ε • at i mᵢ else ε • e₁)
        ≡⟨ ≡.cong₂ (if i == j then_else_) (proj-proj-≡ i m) ε-ε ⟩
          (if i == j then mᵢ else ε)
        ≡⟨⟩
          at i mᵢ j
        ∎
        where open ≡.≡-Reasoning

      w₂αj≡e₁ : ∀ j → w₂ (α j) ≡ e₁
      w₂αj≡e₁ j = ≡.cong (if_then _ else e₁) (dec-neq (i≢αk j))

      α≗αᵣ : α ≗ αᵣ
      α≗αᵣ j =
        begin
          α j
        ≡⟨⟩
          ql ε (at i mᵢ) j
        ≡⟨ ql-cong₂ (λ k → Δw₂≗at k) j ⟨
          ql ε (Δ w₂) j
        ≡⟨ qr-ql-ee w₂ j ⟩
          ql ε (w₂ (ql ε (d w₂) j)) (qr ε (d w₂) j)
        ≡⟨ ≡.cong₂ (λ j' k' → ql ε (w₂ j') k')
            (ql-cong₂ dw₂≗at j)
            (qr-cong₂ dw₂≗at j) ⟩
          ql ε (w₂ (α j)) (αᵣ j)
        ≡⟨ ≡.cong (λ v → ql ε v (αᵣ j)) (w₂αj≡e₁ j) ⟩
          ql ε e₁ (αᵣ j)
        ≡⟨ ql-inner-ε ε (αᵣ j) ⟩
          αᵣ j
        ∎
        where open ≡.≡-Reasoning
      
      w₃ : I → I → M
      w₃ j = if i == j then at i mᵢ else but i mᵢ

      Δw₃≗const-mᵢ : Δ w₃ ≗ F.const mᵢ
      Δw₃≗const-mᵢ j =
        begin
          Δ w₃ j
        ≡⟨ case-apply₁ (i == j) _ _ ⟩
          (if i == j then at i mᵢ j else but i mᵢ j)
        ≡⟨ rewrite-under-if-else i j
              (λ i≡j → ≡.cong (if_then mᵢ else ε) (dec-eq i≡j))
              (λ i≢j → ≡.cong (if_then ε else mᵢ) (dec-neq i≢j)) ⟩
          (if i == j then mᵢ else mᵢ)
        ≡⟨ if-dud ⟩
          mᵢ
        ∎
        where open ≡.≡-Reasoning
      
      dw₃≗at : d w₃ ≗ at i mᵢ
      dw₃≗at j =
        begin
          d w₃ j
        ≡⟨ case-apply₂ (i == j) (ε •_) ⟩
          (if i == j then ε • at i mᵢ else ε • but i mᵢ)
        ≡⟨ ≡.cong₂ (if i == j then_else_) (proj-proj-≡ i m) (ε•but-proj m i) ⟩
          (if i == j then mᵢ else ε)
        ≡⟨⟩
          at i mᵢ j
        ∎
        where open ≡.≡-Reasoning
      
      w₃αj≡but : ∀ {j} → w₃ (α j) ≡ but i mᵢ
      w₃αj≡but {j} = ≡.cong (if_then _ else but i mᵢ) (dec-neq (i≢αk j))
      
      βᵣ-αᵣ-id : ∀ j → j ≡ βᵣ (αᵣ j)
      βᵣ-αᵣ-id j =
        begin
          j
        ≡⟨ qr-outer-ε mᵢ j ⟨
          qr ε (F.const mᵢ) j
        ≡⟨ qr-cong₂ Δw₃≗const-mᵢ j ⟨
          qr ε (Δ w₃) j
        ≡⟨ qr-qr-ee w₃ j ⟩
          qr ε (w₃ (ql ε (d w₃) j)) (qr ε (d w₃) j)
        ≡⟨ ≡.cong₂ (λ j' k' → qr ε (w₃ j') k')
           (ql-cong₂ dw₃≗at j)
           (qr-cong₂ dw₃≗at j) ⟩
          qr ε (w₃ (α j)) (αᵣ j)
        ≡⟨ ≡.cong (λ v → qr ε v (αᵣ j)) w₃αj≡but ⟩
          qr ε (but i mᵢ) (αᵣ j)
        ≡⟨⟩
          βᵣ (αᵣ j)
        ∎
        where
          open ≡.≡-Reasoning

      -- αᵣ is a right inverse of βᵣ 
      Invʳ-βᵣ-αᵣ : Invʳ βᵣ αᵣ
      Invʳ-βᵣ-αᵣ j = ≡.sym (βᵣ-αᵣ-id j) 

      -- ... which then implies αᵣ is the inverse of βᵣ
      Invˡ-βᵣ-αᵣ : Invˡ βᵣ αᵣ
      Invˡ-βᵣ-αᵣ = Fin-lemmata.Invʳ→Invˡ βᵣ αᵣ Invʳ-βᵣ-αᵣ

      -- ... which then implies α = αᵣ is surjective,
      -- and in fact there's (k := βᵣ i) s.t. i≡αk
      i≡αβᵣi : i ≡ α (βᵣ i)
      i≡αβᵣi =
        begin
          i
        ≡⟨ Invˡ-βᵣ-αᵣ i ⟨
          αᵣ (βᵣ i)
        ≡⟨ α≗αᵣ (βᵣ i) ⟨
          α (βᵣ i)
        ∎
        where open ≡.≡-Reasoning

      -- ... which contradicts to the hypothesis.
      bad : ⊥
      bad = i≢αk (βᵣ i) i≡αβᵣi
    
    -- Therefore, the inverse of α exists.
    α-inverse : ∃ λ α⁻¹ → Invᵇ α α⁻¹
    α-inverse with α⁻¹i-or-not
    ... | yes proof    = exist-case.there-is-α⁻¹ proof
    ... | no  disproof = ⊥-elim (not-exist-case.bad disproof)
    
  -- Use single-position case to show generic case:
  -- `ql ε v` has an inverse.
  -- 
  -- It is enough to show for (v := λ j → proj j m),
  -- because `ql ε (λ j → proj j (ε • v)) ≗ ql ε v`.
  module ql-m-inv (m : M) where
    private
      v : I → M
      v j = proj j m
  
    -- `h` has the inverese `g` defined below.
    h : I → I
    h = ql ε v

    private
      hᵣ : I → I
      hᵣ = qr ε v

      -- definitions
      σ : I → I → I
      σ i = ql ε (at i (v i))

      σ-has-inv : ∀ i → ∃ λ f → Invᵇ (σ i) f
      σ-has-inv i = single-position.α-inverse i m

      σ⁻¹ : I → I → I
      σ⁻¹ i = proj₁ (σ-has-inv i)

      σ-σ⁻¹ : ∀ i j → σ i (σ⁻¹ i j) ≡ j
      σ-σ⁻¹ i = proj₁ (proj₂ (σ-has-inv i))

      σ⁻¹-σ : ∀ i j → σ⁻¹ i (σ i j) ≡ j
      σ⁻¹-σ i = proj₂ (proj₂ (σ-has-inv i))
    
    -- This g is the inverse of h
    g : I → I
    g k = qr ε (at k m) (σ⁻¹ k k)
  
    private
      w₄ : I → I → M
      w₄ i = at i (v i)

      Δw₄≗v : Δ w₄ ≗ v
      Δw₄≗v j = ≡.cong (if_then v j else ε) (dec-refl {i = j})

      dw₄≗v : d w₄ ≗ v
      dw₄≗v j = proj-proj-≡ j m

      h-σhᵣ : ∀ j → h j ≡ σ (h j) (hᵣ j)
      h-σhᵣ j =
        begin
          h j
        ≡⟨ ql-cong₂ Δw₄≗v j ⟨
          ql ε (Δ w₄) j
        ≡⟨ qr-ql-ee w₄ j ⟩
          ql ε (w₄ (ql ε (d w₄) j)) (qr ε (d w₄) j)
        ≡⟨ ≡.cong₂ (λ j' k' → ql ε (w₄ j') k')
            (ql-cong₂ dw₄≗v j)
            (qr-cong₂ dw₄≗v j) ⟩
          ql ε (w₄ (h j)) (hᵣ j)
        ≡⟨⟩
          σ (h j) (hᵣ j)
        ∎
        where open ≡.≡-Reasoning
      
      hᵣ-σ⁻¹h : ∀ j → hᵣ j ≡ σ⁻¹ (h j) (h j)
      hᵣ-σ⁻¹h j =
        begin
          hᵣ j
        ≡⟨ σ⁻¹-σ (h j) (hᵣ j) ⟨
          σ⁻¹ (h j) (σ (h j) (hᵣ j))
        ≡⟨ ≡.cong (σ⁻¹ (h j)) (h-σhᵣ j) ⟨
          σ⁻¹ (h j) (h j)
        ∎
        where open ≡.≡-Reasoning
      
      w₅ : I → I → M
      w₅ i = at i m

      Δw₅≗const-m : Δ w₅ ≗ F.const m
      Δw₅≗const-m j = ≡.cong (if_then _ else _) (dec-refl {i = j})

      _ : d w₅ ≡ v
      _ = ≡.refl

    gh-id : ∀ j → g (h j) ≡ j
    gh-id j =
      begin
        g (h j)
      ≡⟨⟩
        qr ε (at (h j) m) (σ⁻¹ (h j) (h j))
      ≡⟨ ≡.cong (qr ε (w₅ (h j))) (hᵣ-σ⁻¹h j) ⟨
        qr ε (w₅ (h j)) (hᵣ j)
      ≡⟨⟩
        qr ε (w₅ (ql ε (d w₅) j)) (qr ε (d w₅) j)
      ≡⟨ qr-qr-ee w₅ j ⟨
        qr ε (Δ w₅) j
      ≡⟨ qr-cong₂ Δw₅≗const-m j ⟩
        qr ε (F.const m) j
      ≡⟨ qr-outer-ε m j ⟩
        j
      ∎
      where
        open ≡.≡-Reasoning
  
  module ql-v-inv (v : I → M) where
    module m-inv = ql-m-inv (ε • v)
    open m-inv
    open m-inv using (g) public

    g-ql-id : Invʳ g (ql ε v)
    g-ql-id j =
      begin
        g (ql ε v j)
      ≡⟨ ≡.cong g (ql-ε-proj j v) ⟨
        g (h j)
      ≡⟨ gh-id j ⟩
        j
      ∎
      where open ≡.≡-Reasoning

    -- g is the inverse of (ql ε v)
    ql-inv-correct : F.Inverseᵇ _≡_ _≡_ (ql ε v) g
    ql-inv-correct =
      Inv-to-Inverse (Fin-lemmata.Invˡ→Invᵇ (ql ε v) g g-ql-id)

  leftIso : LeftIso raw
  leftIso = record {
      ql⁻¹ = ql-v-inv.g;
      ql⁻¹-correct = ql-v-inv.ql-inv-correct
    }