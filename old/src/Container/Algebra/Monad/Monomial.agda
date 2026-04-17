{-# OPTIONS --without-K --safe #-}

-- Monad (uustalu-style) on "monomial" containers.
-- 
-- Naming convention is to add ' (single quote) to
-- corresponding names of Container.Algebra.Monad.
module Container.Algebra.Monad.Monomial where

open import Level

import Function as F
open F using (_∘′_)
import Data.Product as Prod
open Prod using (_×_; proj₁; proj₂; _,_)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core

open import Container.Algebra.Monad.Uustalu

private
  variable
    s p : Level

private
  cong-apply : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    → (f : A → C) (g : B → C) {h : A → B} → (f ≗ g ∘′ h)
    → {x : A} {y : B} → (h x ≡ y)
    → f x ≡ g y
  cong-apply f g f≗gh {x = x} hx≡y = ≡.trans (f≗gh x) (≡.cong g hx≡y)

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

-- Constructor of monomial container

_▷′_ : Set s → Set p → Container s p
_▷′_ S I = S ▷ F.const I

open import Container.Morphism.Equality using (_≈_)
open import Container.Morphism.Iso

record IsMonadMorphism' {S T : Set s} {I J : Set p}
  (rawC : RawMonad' S I)
  (rawD : RawMonad' T J)
  (τ : (S ▷′ I) ⇒ (T ▷′ J))
  : Set (s ⊔ p) where

  module C = RawMonad' rawC
  module D = RawMonad' rawD
  
  τ₀ : S → T
  τ₀ = _⇒_.shape τ
  
  τ₁ : S → J → I
  τ₁ s = _⇒_.position τ {s}

  field
    preserve-ε : τ₀ C.ε ≡ D.ε
    preserve-• : ∀ (s : S) (v : I → S)
      → τ₀ (s C.• v) ≡ τ₀ s D.• (τ₀ ∘′ v ∘′ τ₁ s)
    preserve-ql : ∀ (s : S) (v : I → S)
      → (let Cql = C.ql s v)
        (let Dql = D.ql (τ₀ s) (τ₀ ∘′ v ∘′ τ₁ s))
      → (j : J)
      → Cql (τ₁ (s C.• v) j) ≡ τ₁ s (Dql j)
    preserve-qr : ∀ (s : S) (v : I → S)
      → (let Cqr = C.qr s v)
        (let Dql = D.ql (τ₀ s) (τ₀ ∘′ v ∘′ τ₁ s))
        (let Dqr = D.qr (τ₀ s) (τ₀ ∘′ v ∘′ τ₁ s))
      → (j : J)
      → Cqr (τ₁ (s C.• v) j) ≡ τ₁ (v (τ₁ s (Dql j))) (Dqr j)

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

-- Transferring monomial monad via isomorphisms
module _ {S T : Set s} {I J : Set p}
  (iso : (S ▷′ I) ⇔ (T ▷′ J)) where

  transferRawMonad' : RawMonad' S I → RawMonad' T J
  transferRawMonad' raw' = fromRawMonad (transferRawMonad iso (toRawMonad raw'))

  transferIsMonad' : { raw' : RawMonad' S I } (law : IsMonad' S I raw')
    → IsMonad' T J (transferRawMonad' raw')
  transferIsMonad' { raw' = raw' } law' = fromIsMonad raw₂ law₂
    where
      raw₁ = toRawMonad raw'
      raw₂ = transferRawMonad iso raw₁
      law₁ = toIsMonad raw' law'
      law₂ = transferIsMonad iso law₁

-- Various properties
module IsMonad'-consequences
  {S : Set s} {I : Set p} {raw' : RawMonad' S I}
  (isMonad' : IsMonad' S I raw') where
  open RawMonad' raw'
  open IsMonad' isMonad'
  
  e₁ : I → S
  e₁ = F.const ε

  ε-ε : ε • e₁ ≡ ε
  ε-ε = •-ε ε

  Δ : (I → I → S) → I → S
  Δ w i = w i i

  d : (I → I → S) → I → S
  d w i = ε • w i

  diag-ee : ∀ (w : I → I → S) → diag ε e₁ w ≗ Δ w
  diag-ee w j = ≡.cong₂ w (ql-inner-ε _ _) (qr-outer-ε _ _)

  ε•-ε• : ∀ (w : I → I → S)
    → (ε • λ i → ε • w i) ≡ ε • Δ w
  ε•-ε• w =
    begin
      (ε • λ i → ε • w i)
    ≡⟨ •-• ε e₁ w ⟨
      (ε • e₁) • diag ε e₁ w
    ≡⟨ ≡.cong (_• diag ε e₁ w) ε-ε ⟩
      ε • diag ε e₁ w
    ≡⟨ •-cong₂ (diag-ee w) ⟩
      ε • Δ w
    ∎
    where open ≡.≡-Reasoning

  ql-ql-ee : ∀ (w : I → I → S) (j : I) →
    ql ε (Δ w) j ≡ ql ε (d w) j
  ql-ql-ee w j =
    begin
      ql ε (Δ w) j
    ≡⟨ ≡.cong (λ e → ql e _ _) ε-ε ⟨
      ql (ε • e₁) (Δ w) j
    ≡⟨ ql-cong₂ (diag-ee w) j ⟨
      ql (ε • e₁) (diag ε e₁ w) j
    ≡⟨ ql-inner-ε ε _ ⟨
      ql ε e₁ (ql (ε • e₁) (diag ε e₁ w) j)
    ≡⟨ ql-ql ε e₁ w j ⟩
      ql ε (d w) j
    ∎
    where open ≡.≡-Reasoning

  qr-ql-ee : ∀ (w : I → I → S) (j : I) →
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
  
  qr-qr-ee : ∀ (w : I → I → S) (j : I) →
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