{-# OPTIONS --without-K --safe #-}

open import Level

import Function as F
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

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core
open import Container.Algebra.Monad.Monomial

-- Monomial monad + decidable equality on `I`
module Container.Algebra.Monad.Monomial.DecidableEquality
  {m p} {M : Set m} {I : Set p}
  (_≟_ : DecidableEquality I) where

-- Lemmata

module bool-lemmata {ℓ} {A : Set ℓ} where
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
open bool-lemmata

module DecEq-lemmata where
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
open DecEq-lemmata

-- Preliminary definitions and properties

module preliminary
  {raw : RawMonad' M I}
  (law : IsMonad' M I raw) where

  open RawMonad' raw
  open IsMonad' law
  open IsMonad'-consequences law

  α : I → M → I → M
  α i m j = if ⌊ i ≟ j ⌋ then m else ε

  β : I → M → I → M
  β i m j = if ⌊ i ≟ j ⌋ then ε else m

  -- projection
  infixl 9 _at_
  _at_ : M → I → M
  _at_ m i = ε • α i m


  at-ε : ∀ (i : I) → ε at i ≡ ε
  at-ε i =
    begin
      ε at i
    ≡⟨⟩
      ε • (λ j → if i == j then ε else ε)
    ≡⟨ •-cong₂ (λ _ → if-dud) ⟩
      ε • (λ j → ε)
    ≡⟨ ε-ε ⟩
      ε
    ∎
    where open ≡.≡-Reasoning

  at-ε• : ∀ (v : I → M) (i : I)  →
    (ε • v) at i ≡ (v i) at i
  at-ε• v i =
    begin
      (ε • v) at i
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
      (v i) at i
    ∎
    where
      open ≡.≡-Reasoning

  at-at : ∀ (m : M) (i j : I) →
    m at i at j
      ≡
    (if (i == j) then m at i else ε)
  at-at m i j =
    begin
      m at i at j
    ≡⟨⟩
      (ε • α i m) at j
    ≡⟨ at-ε• (α i m) j ⟩
      (α i m j) at j
    ≡⟨ case-apply₂ (i == j) (_at j) ⟩
      (if (i == j) then m at j else ε at j)
    ≡⟨ rewrite-under-if i j (λ eq → ≡.cong (m at_) (≡.sym eq)) ⟩
      (if (i == j) then m at i else ε at j)
    ≡⟨ ≡.cong (if (i == j) then m at i else_) (at-ε j) ⟩
      (if (i == j) then m at i else ε)
    ∎
    where
      open ≡.≡-Reasoning

  at-at-≡ : ∀ (m : M) (i : I) → m at i at i ≡ m at i
  at-at-≡ m i = ≡.trans (at-at m i i) (≡.cong (if_then m at i else ε) dec-refl)

  at-at-≢ : ∀ (m : M) {i j : I} (_ : i ≢ j) → m at i at j ≡ ε
  at-at-≢ m {i} {j} i≢j =
    ≡.trans (at-at m i j) (≡.cong (if_then m at i else ε) (dec-neq i≢j))

  ε•-at : ∀ (m : M) → ε • (m at_) ≡ m
  ε•-at m =
    begin
      (ε • λ i → m at i)
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
  
  ql-ε-at : ∀ (v : I → M) (i : I) → ql ε ((ε • v) at_) i ≡ ql ε v i
  ql-ε-at v i =
    let open ≡.≡-Reasoning in
    begin
      ql ε (n at_) i
    ≡⟨ ≡.cong (λ e → ql e (n at_) i) ε-ε ⟨
      ql (ε • e₁) (n at_) i
    ≡⟨ ql-cong₂ diag-w i ⟨
      ql (ε • e₁) (diag ε e₁ w) i
    ≡⟨ ql-inner-ε ε _ ⟨
      ql ε e₁ (ql (ε • e₁) (diag ε e₁ w) i)
    ≡⟨ ql-ql ε e₁ w i ⟩
      ql ε (zip e₁ w) i
    ≡⟨⟩
      ql ε (λ j → ε • (v j at_)) i
    ≡⟨ ql-cong₂ (λ j → ε•-at (v j)) i ⟩
      ql ε v i
    ∎
    where
      e₁ : I → M
      e₁ = F.const ε
      
      n : M
      n = ε • v
      
      w : I → I → M
      w j k = v j at k

      diag-w : diag ε e₁ w ≗ (n at_)
      diag-w j =
        let open ≡.≡-Reasoning in
        begin
          diag ε e₁ w j
        ≡⟨⟩
          w (ql ε e₁ j) (qr ε e₁ j)
        ≡⟨ ≡.cong₂ w (ql-inner-ε ε j) (qr-outer-ε ε j) ⟩
          w j j
        ≡⟨⟩
          v j at j
        ≡⟨ at-ε• v j ⟨
          n at j
        ∎
      

module factorization
  {raw : RawMonad' M I}
  (law : IsMonad' M I raw) where

  open RawMonad' raw
  open IsMonad' law
  open IsMonad'-consequences law
  open preliminary law

  -- Range of projections ("factors")
  FM : (i : I) → Set m
  FM i = Σ M (λ m → m at i ≡ m)

  -- Product of all factors (FM i).
  -- (we will show later that Factors is isomorphic to M)
  Factors : Set (p ⊔ m)
  Factors = (i : I) → FM i

  -- ... but only up to pointwise, proof-irrelevant equivalence relation!
  EqFactors : Factors → Factors → Set (p ⊔ m)
  EqFactors f g = ∀ (i : I) → proj₁ (f i) ≡ proj₁ (g i)

  -- to product of factors
  factorize : M → ((i : I) → FM i) 
  factorize m i = m at i , at-at-≡ m i

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
        (ε • λ i → m at i)
      ≡⟨ ε•-at m ⟩
        m
      ∎
      where open ≡.≡-Reasoning
    
    isoˡ : ∀ (f : Factors) (m : M) → m ≡ combine f → EqFactors (factorize m) f
    isoˡ f _ ≡.refl j =
      begin
        proj₁ (factorize (combine f) j)
      ≡⟨⟩
        (ε • f₁) at j
      ≡⟨ at-ε• f₁ j ⟩
        (f₁ j) at j
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


---- Relation to StateLike ----

import Container.Algebra.Monad.StateLike as SL
open SL using (RawStateLike; IsStateLike)

module _
  {raw : RawMonad' M I}
  (law : IsMonad' M I raw) where

  open RawMonad' raw
  open IsMonad' law
  open preliminary law

  -- The LeftTrivial condition can be proven from
  -- seemingly more restrictive equation
  ql-ε-id→ql-id :
    (∀ (v : I → M) (i : I) → ql ε v i ≡ i) → SL.LeftTrivial raw
  ql-ε-id→ql-id ql-ε-id m v i =
    begin
      ql m v i
    ≡⟨ ≡.cong (λ m → ql m v i) (ε•-at m) ⟨
      ql (ε • m at_) v i
    ≡⟨ ql-cong₂ diagw≗v i ⟨
      ql (ε • m at_) (diag ε (m at_) w) i
    ≡⟨ ql-ε-id (m at_) _ ⟨
      ql ε (m at_) (ql (ε • m at_) (diag ε (m at_) w) i)
    ≡⟨ ql-ql ε (m at_) w i ⟩
      ql ε (zip (m at_) w) i
    ≡⟨ ql-ε-id _ i ⟩
      i
    ∎
    where
      open ≡.≡-Reasoning

      w : I → I → M
      w j _ = v j

      diagw≗v : {v₂ : I → M} (j : I) → diag ε v₂ w j ≡ v j
      diagw≗v {v₂} j =
        begin
          diag ε v₂ w j
        ≡⟨⟩
          v (ql ε v₂ j)
        ≡⟨ ≡.cong v (ql-ε-id v₂ j) ⟩
          v j
        ∎

-- When `ql ε v` is automorphism (bijective endomorphism)
-- `I → I`, then one can construct
-- monomial monad isomorphic to the original one
-- which satisfies LeftTrivial.

record LeftIso (raw : RawMonad' M I) : Set (m ⊔ p) where
  open RawMonad' raw using (ε; ql)
  field
    ql⁻¹ : (I → M) → I → I
    ql⁻¹-correct : ∀ (v : I → M) → F.Inverseᵇ _≡_ _≡_ (ql ε v) (ql⁻¹ v)

  ql-ql⁻¹ : ∀ (v : I → M) (i : I) → ql ε v (ql⁻¹ v i) ≡ i
  ql-ql⁻¹ v i = proj₁ (ql⁻¹-correct v) ≡.refl

  ql⁻¹-ql : ∀ (v : I → M) (i : I) → ql⁻¹ v (ql ε v i) ≡ i
  ql⁻¹-ql v i = proj₂ (ql⁻¹-correct v) ≡.refl

open import Container.Morphism.Equality
open import Container.Morphism.Iso

module LeftIso→StateLike
  {raw : RawMonad' M I}
  (law : IsMonad' M I raw)
  (leftIso : LeftIso raw) where

  open RawMonad' raw
  open IsMonad' law
  open preliminary law
  open LeftIso leftIso

  private
    σ : M → I → I
    σ m = ql ε (m at_)

    σ⁻¹ : M → I → I
    σ⁻¹ m = ql⁻¹ (m at_)

    σ-σ⁻¹ : ∀ (m : M) (i : I) → σ m (σ⁻¹ m i) ≡ i
    σ-σ⁻¹ m = ql-ql⁻¹ (m at_)
    
    σ⁻¹-σ : ∀ (m : M) (i : I) → σ⁻¹ m (σ m i) ≡ i
    σ⁻¹-σ m = ql⁻¹-ql (m at_)
    
    -- σ defines automorphism on monomial container (M ▷′ I)
    shift : (M ▷′ I) ⇒ (M ▷′ I)
    shift = F.id ▷ λ {m} i → σ⁻¹ m i

    unshift : (M ▷′ I) ⇒ (M ▷′ I)
    unshift = F.id ▷ λ {m} i → σ m i
    
  shift-iso : (M ▷′ I) ⇔ (M ▷′ I)
  shift-iso = mk⇔ shift unshift
    (mk≈ (λ _ → ≡.refl) (λ m i → σ-σ⁻¹ m i))
    (mk≈ (λ _ → ≡.refl) (λ m i → σ⁻¹-σ m i))

  private
    _•′_ : M → (I → M) → M
    _•′_ m v = m • (v F.∘′ σ m)

    ql′ : M → (I → M) → I → I
    ql′ m v i = σ m (ql m (v F.∘′ σ m) (σ⁻¹ (m •′ v) i))

    qr′ : M → (I → M) → I → I
    qr′ m v i = σ (v (ql′ m v i)) (qr m (v F.∘′ σ m) (σ⁻¹ (m •′ v) i))

  raw-triv : RawMonad' M I
  raw-triv = record {
      ε = ε;
      _•_ = _•′_;
      ql = ql′;
      qr = qr′
    }

  -- raw-triv is (definitionally) raw transferred via shift-iso
  _ : raw-triv ≡ transferRawMonad' shift-iso raw
  _ = ≡.refl

  isMonad-triv : IsMonad' M I raw-triv
  isMonad-triv = transferIsMonad' shift-iso law

  private
    σ-ε-id : ∀ i → σ ε i ≡ i
    σ-ε-id i =
      begin
        σ ε i
      ≡⟨⟩ 
        ql ε (ε at_) i
      ≡⟨ ql-cong₂ at-ε i ⟩
        ql ε (F.const ε) i
      ≡⟨ ql-inner-ε ε i ⟩
        i
      ∎ 
      where open ≡.≡-Reasoning
    
    ε•′ : ∀ v → ε •′ v ≡ ε • v
    ε•′ v =
      begin
        ε •′ v
      ≡⟨⟩
        ε • (v F.∘ σ ε)
      ≡⟨ •-cong₂ (λ i → ≡.cong v (σ-ε-id i)) ⟩
        ε • v
      ∎
      where open ≡.≡-Reasoning

    ql′-ε-id : ∀ (v : I → M) (i : I) → ql′ ε v i ≡ i
    ql′-ε-id v i =
      begin
        ql′ ε v i
      ≡⟨⟩
        σ ε (ql ε (v F.∘′ σ ε) (σ⁻¹ (ε •′ v) i))
      ≡⟨ σ-ε-id _ ⟩
        ql ε (v F.∘′ σ ε) (σ⁻¹ (ε •′ v) i)
      ≡⟨ ql-cong₂ (λ i → ≡.cong v (σ-ε-id i)) _ ⟩
        ql ε v (σ⁻¹ (ε •′ v) i)
      ≡⟨ ≡.cong (λ m′ → ql ε v (σ⁻¹ m′ i)) (ε•′ v) ⟩
        ql ε v (σ⁻¹ (ε • v) i)
      ≡⟨ ql-ε-at v _ ⟨
        ql ε ((ε • v) at_) (σ⁻¹ (ε • v) i)
      ≡⟨⟩
        σ (ε • v) (σ⁻¹ (ε • v) i)
      ≡⟨ σ-σ⁻¹ _ _ ⟩
        i
      ∎
      where open ≡.≡-Reasoning
  
  -- raw-triv satisfy LeftTrivial
  ql′-id : SL.LeftTrivial raw-triv
  ql′-id = ql-ε-id→ql-id isMonad-triv ql′-ε-id

  -- It is already shown that Monomial + LeftTrivial ⇔ StateLike
  rawSL : SL.RawStateLike M I
  rawSL = SL.fromMonomial.rawSL raw-triv ql′-id

  isSL : SL.IsStateLike M I rawSL
  isSL = SL.fromMonomial.fromIsMonad' raw-triv ql′-id isMonad-triv