{-# OPTIONS --without-K --safe #-}

open import Level

open import Function as F
  using (_∘_)

import Data.Product as Prod
open Prod using (∃; Σ; proj₁; proj₂; _,_)

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
import Data.Container.Combinator as CC

-- Set and Container with Reader actions
module Container.Algebra.Reader
  {ℓ} {I : Set ℓ} where

diag : ∀ {m} {M : Set m} → (I → I → M) → I → M
diag w i = w i i

record ReaderAlg0 {m} (M : Set m) : Set (ℓ ⊔ m) where
  field
    base : M
    alg  : (I → M) → M

  field
    -- alg treats functions extentionally
    alg-cong : {f g : I → M} → (f ≗ g) → alg f ≡ alg g

    -- alg respects Reader monad
    alg-pure : {m : M} → alg (F.const m) ≡ m
    alg-join : (h : I → I → M) → alg (diag h) ≡ alg (alg ∘ h)

record ReaderAlg {m p} (C : Container m p) : Set (ℓ ⊔ m ⊔ p) where
  open Container C renaming (Shape to M; Position to P)
  field
    readerAlg0 : ReaderAlg0 M
  
  open ReaderAlg0 readerAlg0 public

  field
    ↖ : {v : I → M} → P (alg v) → I
    ↗ : {v : I → M} → (p : P (alg v)) → P (v (↖ p))

    ↖-cong : {f g : I → M}
      → (eq : f ≗ g)
      → (p : P (alg f))
      → ↖ p ≡ ↖ (≡.subst P (alg-cong eq) p)
    ↗-cong : {f g : I → M}
      → (eq : f ≗ g)
      → (p : P (alg f))
      → (let fp≡gp = ≡.trans (eq (↖ p)) (≡.cong g (↖-cong eq p)))
      → ≡.subst P fp≡gp (↗ p) ≡ ↗ (≡.subst P (alg-cong eq) p)

    -- ql,qr respects Reader monad
    ↗-pure : (m : M) (p : P (alg (F.const m)))
      → ↗ p ≡ ≡.subst P alg-pure p

    ↖-↖ : {w : I → I → M}
      → {p : P (alg (diag w))} {q : P (alg (alg ∘ w))}
      → (p≡q : ≡.subst P (alg-join w) p ≡ q)
      → ↖ p ≡ ↖ q
    ↗-↖ : {w : I → I → M}
      → {p : P (alg (diag w))} {q : P (alg (alg ∘ w))}
      → (p≡q : ≡.subst P (alg-join w) p ≡ q)
      → ↖ p ≡ ↖ (↗ q)
    ↗-↗ : {w : I → I → M}
      → {p : P (alg (diag w))} {q : P (alg (alg ∘ w))}
      → (p≡q : ≡.subst P (alg-join w) p ≡ q)
      → (let eq₁ = ↖-↖ p≡q)
        (let eq₂ = ↗-↖ p≡q)
      → ≡.subst₂ (λ j k → P (w j k)) eq₁ eq₂ (↗ p) ≡ ↗ (↗ q)

module WithDecEq0
  (_≟_ : DecidableEquality I)
  {m} {M : Set m} (RA : ReaderAlg0 M) where

  open import Data.Bool.IfThenElseProperties
  open import Relation.Binary.DecidableEquality.Util _≟_
  open ReaderAlg0 RA

  at : I → M → I → M
  at i m j = if ⌊ i ≟ j ⌋ then m else base

  but : I → M → I → M
  but i m j = if ⌊ i ≟ j ⌋ then base else m

  -- projection
  proj : I → M → M
  proj i m = alg (at i m)

  proj-base : ∀ (i : I) → proj i base ≡ base
  proj-base i =
    begin
      proj i base
    ≡⟨⟩
      alg (λ j → if i == j then base else base)
    ≡⟨ alg-cong (λ _ → if-dud) ⟩
      alg (λ j → base)
    ≡⟨ alg-pure ⟩
      base
    ∎
    where open ≡.≡-Reasoning

  proj-alg : ∀ (v : I → M) (i : I) →
    proj i (alg v) ≡ proj i (v i)
  proj-alg v i =
    begin
      proj i (alg v)
    ≡⟨⟩
      alg (at i (alg v))
    ≡⟨⟩
      alg (λ j → if i == j then alg v else base)
    ≡⟨ alg-cong (λ j → ≡.cong (if i == j then alg v else_) (≡.sym alg-pure)) ⟩
      alg (λ j → if i == j then alg v else (alg (F.const base)))
    ≡⟨ alg-cong (λ j → case-apply₂ (i == j) alg) ⟨
      alg (λ j → alg (if i == j then v else F.const base))
    ≡⟨ alg-join (λ j → if i == j then _ else _) ⟨
      alg (λ j → (if i == j then v else F.const base) j)
    ≡⟨ alg-cong (λ j → case-apply₁ (i == j) _ _) ⟩
      alg (λ j → if i == j then v j else base)
    ≡⟨ alg-cong (λ j →
      rewrite-under-if i j (λ eq → ≡.cong v (≡.sym eq)))
    ⟩
      alg (λ j → if i == j then v i else base)
    ≡⟨⟩
      proj i (v i)
    ∎
    where
      open ≡.≡-Reasoning

  proj-proj : ∀ (i j : I) (m : M) →
    proj j (proj i m)
      ≡
    (if (i == j) then proj i m else base)
  proj-proj i j m =
    begin
      proj j (proj i m)
    ≡⟨⟩
      proj j (alg (at i m))
    ≡⟨ proj-alg (at i m) j ⟩
      proj j (at i m j)
    ≡⟨ case-apply₂ (i == j) (proj j) ⟩
      (if (i == j) then proj j m else proj j base)
    ≡⟨ rewrite-under-if-else i j
          (λ eq → ≡.cong (λ k → proj k m) (≡.sym eq))
          (λ _ → proj-base j) ⟩
      (if (i == j) then proj i m else base)
    ∎
    where
      open ≡.≡-Reasoning

  proj-proj-≡ : ∀ (i : I) (m : M)  → proj i (proj i m) ≡ proj i m
  proj-proj-≡ i m = ≡.trans (proj-proj i i m) (≡.cong (if_then proj i m else base) dec-refl)

  proj-proj-≢ : ∀{i j : I} (_ : i ≢ j)  (m : M) → proj j (proj i m) ≡ base
  proj-proj-≢ {i} {j} i≢j m =
    ≡.trans (proj-proj i j m) (≡.cong (if_then proj i m else base) (dec-neq i≢j))

  alg-proj : ∀ (m : M) → alg (λ i → proj i m) ≡ m
  alg-proj m =
    begin
      (alg λ i → proj i m)
    ≡⟨⟩
      (alg λ i → alg (at i m))
    ≡⟨ alg-join (λ i j → at i m j) ⟨
      (alg λ i → at i m i)
    ≡⟨⟩
      (alg λ i → if i == i then m else base)
    ≡⟨ alg-cong (λ i → ≡.cong (if_then m else base) dec-refl) ⟩
      (alg λ i → m)
    ≡⟨ alg-pure ⟩
      m
    ∎
    where open ≡.≡-Reasoning
  
  algbut-proj : ∀ (m : M) (i : I) → alg (but i (proj i m)) ≡ base
  algbut-proj m i =
    begin
      alg (but i (proj i m))
    ≡⟨⟩
      (alg λ j → if i == j then base else alg (at i m))
    ≡⟨ alg-cong (λ j → ≡.cong (if i == j then_else alg (at i m)) alg-pure) ⟨
      (alg λ j → if i == j then alg (F.const base) else alg (at i m))
    ≡⟨ alg-cong (λ j → case-apply₂ (i == j) alg) ⟨
      (alg λ j → alg (if i == j then F.const base else at i m))
    ≡⟨ alg-join _ ⟨
      (alg λ j → (if i == j then F.const base else at i m) j)
    ≡⟨ alg-cong (λ j → case-apply₁ (i == j) (F.const base) (at i m)) ⟩
      (alg λ j → if i == j then base else (if i == j then m else base))
    ≡⟨ alg-cong (λ j → ≡.trans (if-else-if (i == j)) if-dud) ⟩
      (alg λ i → base)
    ≡⟨ alg-pure ⟩
      base
    ∎
    where open ≡.≡-Reasoning

  module factorization where
    -- Range of projections ("factors")
    FM : (i : I) → Set m
    FM i = Σ M (λ m → proj i m ≡ m)

    -- Product of all factors (FM i).
    -- (we will show later that Factors is isomorphic to M)
    Factors : Set (ℓ ⊔ m)
    Factors = (i : I) → FM i

    -- ... but only up to pointwise, proof-irrelevant equivalence relation!
    EqFactors : Factors → Factors → Set (ℓ ⊔ m)
    EqFactors f g = ∀ (i : I) → proj₁ (f i) ≡ proj₁ (g i)

    -- to product of factors
    factorize : M → ((i : I) → FM i) 
    factorize m i = proj i m , proj-proj-≡ i m

    -- from product of factors
    combine : ((i : I) → FM i) → M
    combine f = alg λ i → proj₁ (f i)

    factorize-cong : F.Congruent _≡_ EqFactors factorize
    factorize-cong ≡.refl _ = ≡.refl

    combine-cong : F.Congruent EqFactors _≡_ combine
    combine-cong f≈g = alg-cong f≈g

    private
      isoʳ : ∀ (m : M) (f : Factors) → EqFactors f (factorize m) → combine f ≡ m
      isoʳ m f f≈ =
        begin
          combine f
        ≡⟨⟩
          (alg λ i → proj₁ (f i))
        ≡⟨ alg-cong f≈ ⟩
          (alg λ i → proj i m)
        ≡⟨ alg-proj m ⟩
          m
        ∎
        where open ≡.≡-Reasoning
      
      isoˡ : ∀ (f : Factors) (m : M) → m ≡ combine f → EqFactors (factorize m) f
      isoˡ f _ ≡.refl j =
        begin
          proj₁ (factorize (combine f) j)
        ≡⟨⟩
          proj j (alg f₁)
        ≡⟨ proj-alg f₁ j ⟩
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

module WithDecEq
  (_≟_ : DecidableEquality I)
  {m p} {C : Container m p} (RA : ReaderAlg C) where

  open import Data.Bool.IfThenElseProperties
  open import Relation.Binary.DecidableEquality.Util _≟_
  open Container C renaming (Shape to M; Position to P)
  open ReaderAlg RA

  open WithDecEq0 _≟_ readerAlg0

  ↖-alg-proj : ∀ {v : I → M}
    → (p : P (alg (λ j → proj j (alg v))))
    → ↖ p ≡ ↖ (≡.subst P (alg-proj (alg v)) p)
  ↖-alg-proj {v} p = begin
      ↖ p
    ≡⟨ ↖-cong (proj-alg v) p ⟩
      ↖ (≡.subst P (alg-cong (proj-alg v)) p)
    ≡⟨ {! ↖-↖ _ !} ⟩
      ↖ (≡.subst P (alg-proj (alg v)) p)
    ∎
    where open ≡.≡-Reasoning

  module factorization1 where
    open factorization
      renaming (Factors to Factors0; EqFactors to EqFactors0)
    
    FP : (i : I) → FM i → Set (ℓ ⊔ p)
    FP i (mᵢ , _) = Σ (P (proj i mᵢ)) (λ p → ↖ p ≡ i)

    FC : (i : I) → Container m (ℓ ⊔ p)
    FC i = FM i ▷ FP i

    Factors : Container (ℓ ⊔ m) (ℓ ⊔ p)
    Factors = CC.Π I FC

    factorizeP : {m : M} → (∃ λ i → FP i (factorize m i)) → P m
    factorizeP {m} (i , (p , ↖p≡i)) = ≡.subst P eq (↗ p')
      where
        p' : P (proj i m)
        p' = ≡.subst P (proj-proj-≡ i m) p

        ↖p'≡i : ↖ p' ≡ i
        ↖p'≡i = begin
            ↖ p'
          ≡⟨⟩
            ↖ (≡.subst P (proj-proj-≡ i m) p)
          ≡⟨ _ ⟩
            _
          ≡⟨ _ ⟩
            ↖ p
          ≡⟨ ↖p≡i ⟩
            i
          ∎
          where open ≡.≡-Reasoning

        eq : at i m (↖ p') ≡ m
        eq = ≡.trans (≡.cong (at i m) ↖p'≡i) elim-if-refl

    factorizeC : C ⇒ Factors
    factorizeC = factorize ▷ factorizeP
