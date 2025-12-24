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
  
  if-then-if : ∀ (cond : Bool) {x y z : A}
    → (if cond then (if cond then x else y) else z) ≡ (if cond then x else z)
  if-then-if false = ≡.refl
  if-then-if true = ≡.refl

  if-else-if : ∀ (cond : Bool) {x y z : A}
    → (if cond then x else (if cond then y else z)) ≡ (if cond then x else z)
  if-else-if false = ≡.refl
  if-else-if true = ≡.refl
open bool-lemmata

module DecEq-lemmata where
  infix 4 _==_

  _==_ : I → I → Bool
  _==_ x y = ⌊ x ≟ y ⌋

  dec-eq : ∀ {i j : I} → (i ≡ j) → (i == j) ≡ true
  dec-eq {i} {j} i≡j with i ≟ j
  ... | yes _ = ≡.refl
  ... | no i≢j = ⊥-elim (i≢j i≡j)

  dec-neq : ∀ {i j : I} → (i ≢ j) → (i == j) ≡ false
  dec-neq {i} {j} i≢j with i ≟ j
  ... | yes i≡j = ⊥-elim (i≢j i≡j)
  ... | no _ = ≡.refl

  dec-refl : ∀ {i : I} → (i == i) ≡ true
  dec-refl = dec-eq ≡.refl

  elim-if-refl : ∀ {i : I} {a} {A : Set a} {x y : A}
    → (if i == i then x else y) ≡ x
  elim-if-refl = ≡.cong (if_then _ else _) dec-refl

  rewrite-under-if : ∀ (i j : I) {a} {A : Set a} {x₁ x₂ y : A}
    → (i ≡ j → x₁ ≡ x₂) → (if i == j then x₁ else y) ≡ (if i == j then x₂ else y)
  rewrite-under-if i j rewriter with i ≟ j
  ... | yes i≡j = rewriter i≡j
  ... | no _ = ≡.refl

  rewrite-under-if-else : ∀ (i j : I) {a}
      {A : Set a} {x₁ x₂ y₁ y₂ : A}
    → (i ≡ j → x₁ ≡ x₂)
    → (i ≢ j → y₁ ≡ y₂)
    → (if i == j then x₁ else y₁) ≡ (if i == j then x₂ else y₂)
  rewrite-under-if-else i j rewriter-x rewriter-y with i ≟ j
  ... | yes i≡j = rewriter-x i≡j
  ... | no i≢j = rewriter-y i≢j

open DecEq-lemmata

-- Preliminary definitions and properties

module preliminary
  {raw : RawMonad' M I}
  (law : IsMonad' M I raw) where

  open RawMonad' raw
  open IsMonad' law
  open IsMonad'-consequences law

  at : I → M → I → M
  at i m j = if ⌊ i ≟ j ⌋ then m else ε

  but : I → M → I → M
  but i m j = if ⌊ i ≟ j ⌋ then ε else m

  -- projection
  proj : I → M → M
  proj i m = ε • at i m

  proj-ε : ∀ (i : I) → proj i ε ≡ ε
  proj-ε i =
    begin
      proj i ε
    ≡⟨⟩
      ε • (λ j → if i == j then ε else ε)
    ≡⟨ •-cong₂ (λ _ → if-dud) ⟩
      ε • (λ j → ε)
    ≡⟨ ε-ε ⟩
      ε
    ∎
    where open ≡.≡-Reasoning

  proj-ε• : ∀ (v : I → M) (i : I) →
    proj i (ε • v) ≡ proj i (v i)
  proj-ε• v i =
    begin
      proj i (ε • v)
    ≡⟨⟩
      ε • at i (ε • v)
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
      proj i (v i)
    ∎
    where
      open ≡.≡-Reasoning

  proj-proj : ∀ (i j : I) (m : M) →
    proj j (proj i m)
      ≡
    (if (i == j) then proj i m else ε)
  proj-proj i j m =
    begin
      proj j (proj i m)
    ≡⟨⟩
      proj j (ε • at i m)
    ≡⟨ proj-ε• (at i m) j ⟩
      proj j (at i m j)
    ≡⟨ case-apply₂ (i == j) (proj j) ⟩
      (if (i == j) then proj j m else proj j ε)
    ≡⟨ rewrite-under-if-else i j
          (λ eq → ≡.cong (λ k → proj k m) (≡.sym eq))
          (λ _ → proj-ε j) ⟩
      (if (i == j) then proj i m else ε)
    ∎
    where
      open ≡.≡-Reasoning

  proj-proj-≡ : ∀ (i : I) (m : M)  → proj i (proj i m) ≡ proj i m
  proj-proj-≡ i m = ≡.trans (proj-proj i i m) (≡.cong (if_then proj i m else ε) dec-refl)

  proj-proj-≢ : ∀{i j : I} (_ : i ≢ j)  (m : M) → proj j (proj i m) ≡ ε
  proj-proj-≢ {i} {j} i≢j m =
    ≡.trans (proj-proj i j m) (≡.cong (if_then proj i m else ε) (dec-neq i≢j))

  ε•-proj : ∀ (m : M) → ε • (λ i → proj i m) ≡ m
  ε•-proj m =
    begin
      (ε • λ i → proj i m)
    ≡⟨⟩
      (ε • λ i → ε • at i m)
    ≡⟨ ε•-ε• (λ i j → at i m j) ⟩
      (ε • λ i → at i m i)
    ≡⟨⟩
      (ε • λ i → if i == i then m else ε)
    ≡⟨ •-cong₂ (λ i → ≡.cong (if_then m else ε) dec-refl) ⟩
      (ε • λ i → m)
    ≡⟨ ε-• m ⟩
      m
    ∎
    where open ≡.≡-Reasoning
  
  ε•but-proj : ∀ (m : M) (i : I) → ε • but i (proj i m) ≡ ε
  ε•but-proj m i =
    begin
      (ε • but i (proj i m))
    ≡⟨⟩
      (ε • λ j → if i == j then ε else ε • at i m)
    ≡⟨ •-cong₂ (λ j → ≡.cong (if i == j then_else ε • at i m) ε-ε) ⟨
      (ε • λ j → if i == j then ε • F.const ε else ε • at i m)
    ≡⟨ •-cong₂ (λ j → case-apply₂ (i == j) (ε •_)) ⟨
      (ε • λ j → ε • (if i == j then F.const ε else at i m))
    ≡⟨ ε•-ε• _ ⟩
      (ε • λ j → (if i == j then F.const ε else at i m) j)
    ≡⟨ •-cong₂ (λ j → case-apply₁ (i == j) (F.const ε) (at i m)) ⟩
      (ε • λ j → if i == j then ε else (if i == j then m else ε))
    ≡⟨ •-cong₂ (λ j → ≡.trans (if-else-if (i == j)) if-dud) ⟩
      (ε • λ i → ε)
    ≡⟨ ε-ε ⟩
      ε
    ∎
    where open ≡.≡-Reasoning

  ql-ε-proj : ∀ (i : I) (v : I → M) → ql ε (λ j → proj j (ε • v)) i ≡ ql ε v i
  ql-ε-proj i v =
    let open ≡.≡-Reasoning in
    begin
      ql ε (λ j → proj j (ε • v)) i
    ≡⟨ ql-cong₂ (proj-ε• v) i ⟩
      ql ε (Δ w) i
    ≡⟨ ql-ql-ee w i ⟩
      ql ε (λ j → ε • w j) i
    ≡⟨ ql-cong₂ (λ j → ε•-proj (v j)) i ⟩
      ql ε v i
    ∎
    where
      n : M
      n = ε • v
      
      w : I → I → M
      w j k = proj k (v j)

module factorization
  {raw : RawMonad' M I}
  (law : IsMonad' M I raw) where

  open RawMonad' raw
  open IsMonad' law
  open IsMonad'-consequences law
  open preliminary law

  -- Range of projections ("factors")
  FM : (i : I) → Set m
  FM i = Σ M (λ m → proj i m ≡ m)

  -- Product of all factors (FM i).
  -- (we will show later that Factors is isomorphic to M)
  Factors : Set (p ⊔ m)
  Factors = (i : I) → FM i

  -- ... but only up to pointwise, proof-irrelevant equivalence relation!
  EqFactors : Factors → Factors → Set (p ⊔ m)
  EqFactors f g = ∀ (i : I) → proj₁ (f i) ≡ proj₁ (g i)

  -- to product of factors
  factorize : M → ((i : I) → FM i) 
  factorize m i = proj i m , proj-proj-≡ i m

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
        (ε • λ i → proj i m)
      ≡⟨ ε•-proj m ⟩
        m
      ∎
      where open ≡.≡-Reasoning
    
    isoˡ : ∀ (f : Factors) (m : M) → m ≡ combine f → EqFactors (factorize m) f
    isoˡ f _ ≡.refl j =
      begin
        proj₁ (factorize (combine f) j)
      ≡⟨⟩
        proj j (ε • f₁)
      ≡⟨ proj-ε• f₁ j ⟩
        proj j (f₁ j)
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
    ≡⟨ ≡.cong (λ m → ql m v i) (ε•-proj m) ⟨
      ql (ε • pm) v i
    ≡⟨ ql-cong₂ diagw≗v i ⟨
      ql (ε • pm) (diag ε pm w) i
    ≡⟨ ql-ε-id pm _ ⟨
      ql ε pm (ql (ε • pm) (diag ε pm w) i)
    ≡⟨ ql-ql ε pm w i ⟩
      ql ε (zip pm w) i
    ≡⟨ ql-ε-id _ i ⟩
      i
    ∎
    where
      open ≡.≡-Reasoning

      pm : I → M
      pm j = proj j m

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
    σ m = ql ε (λ i → proj i m)

    σ⁻¹ : M → I → I
    σ⁻¹ m = ql⁻¹ (λ i → proj i m)

    σ-σ⁻¹ : ∀ (m : M) (i : I) → σ m (σ⁻¹ m i) ≡ i
    σ-σ⁻¹ m = ql-ql⁻¹ (λ i → proj i m)
    
    σ⁻¹-σ : ∀ (m : M) (i : I) → σ⁻¹ m (σ m i) ≡ i
    σ⁻¹-σ m = ql⁻¹-ql (λ i → proj i m)
    
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
        ql ε (λ j → proj j ε) i
      ≡⟨ ql-cong₂ proj-ε i ⟩
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
      ≡⟨ ql-ε-proj _ v ⟨
        ql ε (λ j → proj j (ε • v)) (σ⁻¹ (ε • v) i)
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