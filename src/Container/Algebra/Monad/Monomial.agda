{-# OPTIONS --without-K --safe #-}

-- Monad (uustalu-style) on "monomial" containers
module Container.Algebra.Monad.Monomial where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core

open import Container.Algebra.Monad.Uustalu

private
  variable
    s p : Level

record RawMonad' (S : Set s) (I : Set p) : Set (s ⊔ p) where
  infixr 7 _•_
  
  field
    ε : S
    _•_ : S → (I → S) → S
    ql : S → (I → S) → I → I
    qr : S → (I → S) → I → I

record IsMonad' (S : Set s) (I : Set p) (raw : RawMonad' S I) : Set (s ⊔ p) where
  open RawMonad' raw

  diag : S → (I → S) → (I → I → S) → (I → S)
  diag s v w i = w (ql s v i) (qr s v i)

  zip : (I → S) → (I → I → S) → (I → S)
  zip v w i = v i • w i

  field
    •-cong₂ : ∀ {s : S} {v₁ v₂ : I → S} → (v₁ ≗ v₂) → s • v₁ ≡ s • v₂
    ql-cong₂ : ∀ {s : S} {v₁ v₂ : I → S} → (v₁ ≗ v₂) → ql s v₁ ≗ ql s v₂
    qr-cong₂ : ∀ {s : S} {v₁ v₂ : I → S} → (v₁ ≗ v₂) → qr s v₁ ≗ qr s v₂

    •-ε : ∀ (s : S) → s • F.const ε ≡ s
    ε-• : ∀ (s : S) → ε • F.const s ≡ s
    •-• : ∀ (s : S) (v : I → S) (w : I → I → S)
      → (s • v) • diag s v w ≡ s • zip v w
    
    ql-inner-ε : ∀ (s : S) (i : I)
      → ql s (F.const ε) i ≡ i
    qr-outer-ε : ∀ (s : S) (i : I)
      → qr ε (F.const s) i ≡ i
    
    ql-ql : ∀ (s : S) (v : I → S) (w : I → I → S)
      → (let Δw = diag s v w)
         (let u = zip v w)
      → (i : I)
      → ql s v (ql (s • v) Δw i) ≡ ql s u i
    qr-ql : ∀ (s : S) (v : I → S) (w : I → I → S)
      → (let Δw = diag s v w)
         (let u = zip v w)
      → (i : I)
      → (let j =  ql s u i)
      → qr s v (ql (s • v) Δw i) ≡ ql (v j) (w j) (qr s u i)
    qr-qr : ∀ (s : S) (v : I → S) (w : I → I → S)
      → (let Δw = diag s v w)
         (let u = zip v w)
      → (i : I)
      → (let j = ql s u i)
      → qr (s • v) Δw i ≡ qr (v j) (w j) (qr s u i)

module IsMonad'-consequences
  {S : Set s} {I : Set p} {raw' : RawMonad' S I}
  (isMonad' : IsMonad' S I raw') where
  open RawMonad' raw'
  open IsMonad' isMonad'
  
  ε-ε : ε • F.const ε ≡ ε
  ε-ε = •-ε ε

  ε•-ε• : ∀ (w : I → I → S)
    → (ε • λ i → ε • w i) ≡ ε • λ i → w i i
  ε•-ε• w =
    begin
      (ε • λ i → ε • w i)
    ≡⟨ •-• ε (F.const ε) w ⟨
      (ε • F.const ε) • diag ε (F.const ε) w
    ≡⟨ ≡.cong (_• diag ε (F.const ε) w) ε-ε ⟩
      ε • diag ε (F.const ε) w
    ≡⟨⟩
      (ε • λ i → w (ql ε (F.const ε) i) (qr ε (F.const ε) i))
    ≡⟨ •-cong₂ (λ i → ≡.cong₂ w (ql-inner-ε ε i) (qr-outer-ε ε i)) ⟩
      (ε • λ i → w i i)
    ∎
    where open ≡.≡-Reasoning

-- Utilities

private
  subst-const : ∀ {a b} {A : Set a} {x y : A} (B : Set b) (x≡y : x ≡ y)
    → (p : B) → ≡.subst (F.const B) x≡y p ≡ p
  subst-const _ ≡.refl _ = ≡.refl

  dsubst₂-const : ∀ {a b c} {A : Set a} {B : A → Set b} (C : Set c)
          {x₁ x₂ y₁ y₂} (eqx : x₁ ≡ x₂) (eqy : ≡.subst B eqx y₁ ≡ y₂)
        → (p : C) → ≡.dsubst₂ (λ _ _ → C) eqx eqy p ≡ p
  dsubst₂-const _ ≡.refl ≡.refl _ = ≡.refl

  infixr 8 _⨾_
  _⨾_ : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  _⨾_ = ≡.trans

-- Monomial Monad on (S, I) ↔ Monad on (S, const I)

module _ {S : Set s} {I : Set p} where
  C : Container s p
  C = S ▷ F.const I

  fromRawMonad : RawMonad C → RawMonad' S I
  fromRawMonad raw = record {
      ε = ε;
      _•_ = _•_;
      ql = λ s v p → ↖ {s} {v} p;
      qr = λ s v p → ↗ {s} {v} p 
    }
    where open RawMonad raw
  
  toRawMonad : RawMonad' S I → RawMonad C
  toRawMonad raw' = record {
      ε = ε;
      _•_ = _•_; 
      ↖ = λ {s} {v} p → ql s v p;
      ↗ = λ {s} {v} p → qr s v p 
    }
    where open RawMonad' raw'

  fromIsMonad : (raw : RawMonad C)
    → IsMonad C raw → IsMonad' S I (fromRawMonad raw)
  fromIsMonad raw isMonad = record {
      •-cong₂ = λ v₁≗v₂ → law.•-cong (law.mkEq ≡.refl v₁≗v₂);
      ql-cong₂ = λ v₁≗v₂ p →
        let eq = law.mkEq ≡.refl v₁≗v₂ in
        law.↖-cong eq p ⨾
        ≡.cong ↖ (subst-const I (law.•-cong eq) p) ;
      qr-cong₂ = λ v₁≗v₂ p →
        let eq = law.mkEq ≡.refl v₁≗v₂ in
        ≡.sym (subst-const I _ (↗ p)) ⨾
        law.↗-cong eq p ⨾
        ≡.cong ↗ (subst-const I (law.•-cong eq) p) ;
      •-ε = law.•-ε;
      ε-• = law.ε-•;
      •-• = law.•-•;
      ql-inner-ε = λ s p → law.↖-inner-ε {s} p ⨾ subst-const I _ p;
      qr-outer-ε = λ s p → law.↗-outer-ε {s} p ⨾ subst-const I _ p;
      ql-ql = λ s v w p → law.↖-↖ {s} {v} {w} (subst-const I _ p);
      qr-ql = λ s v w p →
        ≡.sym (subst-const I _ (↗ (↖ p))) ⨾
        law.↗-↖ {s} {v} {w} (subst-const I (law.•-• s v w) p);
      qr-qr = λ s v w p →
        ≡.sym (dsubst₂-const I _ _ (↗ p)) ⨾
        law.↗-↗ {s} {v} {w} (subst-const I (law.•-• s v w) p)
    }
    where
      open RawMonad raw
      module law = IsMonad isMonad
      module newRaw = RawMonad' (fromRawMonad raw)
  
  toIsMonad : (raw' : RawMonad' S I)
    → IsMonad' S I raw' → IsMonad C (toRawMonad raw')
  toIsMonad raw' isMonad' = record { impl }
    where
      raw = toRawMonad raw'
      open RawMonad' raw' hiding (ε; _•_)
      open RawMonad raw hiding (S; P)
      open EqualityDefinition C
      module law' = IsMonad' isMonad'

      module impl where
        P : S → Set p
        P = F.const I
        
        •-cong : ∀ {cx cy : ⟦ C ⟧ S}
          → Eq cx cy → mm cx ≡ mm cy
        •-cong (mkEq ≡.refl v₁≗v₂) = law'.•-cong₂ v₁≗v₂

        ↖-cong : ∀ {cx cy : ⟦ C ⟧ S}
          → (eq : Eq cx cy)
          → ∀ (p : P (mm cx)) → ≡.subst P (shapeEq eq) (↖ p) ≡ ↖ (≡.subst P (•-cong eq) p)
        ↖-cong (mkEq ≡.refl v₁≗v₂) p =
          law'.ql-cong₂ v₁≗v₂ p ⨾ ≡.sym (≡.cong ↖ (subst-const I _ p))

        ↗-cong : ∀ {cx cy : ⟦ C ⟧ S}
          → (eq : Eq cx cy)
          → ∀ (p : P (mm cx))
          → ≡.subst P (cong-apply (proj₂ cx) (proj₂ cy) (positionEq eq) (↖-cong eq p)) (↗ p)
              ≡
            ↗ (≡.subst P (•-cong eq) p)
        ↗-cong (mkEq ≡.refl v₁≗v₂) p =
          subst-const I _ (↗ p) ⨾
          law'.qr-cong₂ v₁≗v₂ p ⨾
          ≡.sym (≡.cong ↗ (subst-const I _ p))

        •-ε : ∀ (s : S) → s • F.const ε ≡ s
        •-ε = law'.•-ε
        ε-• : ∀ (s : S) → ε • F.const s ≡ s
        ε-• = law'.ε-•
        •-• : ∀ (s : S) (v : P s → S) (w : (p : P s) → P (v p) → S)
          → (s • v) • diag w ≡ s • (λ p → v p • w p)
        •-• = law'.•-•
        
        ↖-inner-ε : ∀ {s : S} (p : P (s • F.const ε))
          → ↖ p ≡ ≡.subst P (•-ε s) p
        ↖-inner-ε {s} p = law'.ql-inner-ε s p ⨾ ≡.sym (subst-const I _ p)

        ↗-outer-ε : ∀ {s : S} (p : P (ε • F.const s))
          → ↗ p ≡ ≡.subst P (ε-• s) p
        ↗-outer-ε {s} p = law'.qr-outer-ε s p ⨾ ≡.sym (subst-const I _ p)
        
        ↖-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
          → {p : P ((s • v) • diag {s} {v} w)} {q : P (s • zip {s} v w)}
          → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
          → ↖ (↖ p) ≡ ↖ q
        ↖-↖ {s} {v} {w} {p} {q} ≡.refl =
          law'.ql-ql s v w p ⨾
          ≡.cong ↖ (≡.sym (subst-const I _ p))
        
        ↗-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
          → {p : P ((s • v) • diag {s} {v} w)} {q : P (s • zip {s} v w)}
          → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
          → (let p₁₁≡q₁ = ↖-↖ p≡q)
             (let q₁ = ↖ q)
          → ≡.subst (λ r → P (v r)) p₁₁≡q₁ (↗ {s} {v} (↖ p)) ≡ ↖ {v q₁} {w q₁} (↗ q)
        ↗-↖ {s} {v} {w} {p} {q} ≡.refl =
          subst-const I _ (↗ (↖ p)) ⨾
          law'.qr-ql s v w p ⨾
          ≡.cong (λ r → ↖ {v (↖ r)} {w (↖ r)} (↗ r)) (≡.sym (subst-const I _ p))

        ↗-↗ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
          → {p : P ((s • v) • diag {s} {v} w)} {q : P (s • zip {s} v w)}
          → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
          → (let p₁₁≡q₁ = ↖-↖ p≡q)
             (let p₁₂≡q₂₁ = ↗-↖ p≡q)
             (let q₁ = ↖ q)
          → ≡.dsubst₂ (λ r₁ r₂ → P (w r₁ r₂)) p₁₁≡q₁ p₁₂≡q₂₁ (↗ p)
               ≡
             ↗ {v q₁} {w q₁} (↗ q)
        ↗-↗ {s} {v} {w} {p} {q} ≡.refl =
          dsubst₂-const I _ _ (↗ p) ⨾
          law'.qr-qr s v w p ⨾
          ≡.cong (λ r → ↗ {v (↖ r)} {w (↖ r)} (↗ r)) (≡.sym (subst-const I _ p))