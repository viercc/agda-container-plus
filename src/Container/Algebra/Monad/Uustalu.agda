{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Monad.Uustalu where

open import Level

import Function as F
open F using (_∘′_)
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
import Data.Product.Properties as ProdProp
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core renaming (map to map⟦⟧)
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Morphism using (id; _∘_)

open import Container.Morphism.Equality hiding (Eq)
open import Container.Morphism.Iso

open import Container.Combinator.Compose as Compose using (Id; Comp)

import Container.Algebra.Monad as MM
import Container.Lax as Lax
import Container.Combinator.Compose.Lax as LaxComp

private
  variable
    s p : Level

record RawMonad (C : Container s p) : Set (s ⊔ p) where
  open Container C renaming (Shape to S; Position to P) public

  infixr 7 _•_
  
  field
    ε : S
    _•_ : (s : S) → (P s → S) → S
    ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
    ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))
  
  diag : {s : S} {v : P s → S} (w : (p₁ : P s) → P (v p₁) → S)
    → P (s • v) → S
  diag {s} {v} w p = w (↖ p) (↗ p)

  zip : {s : S} (v : P s → S) (w : (p₁ : P s) → P (v p₁) → S) →
    P s → S
  zip v w p = v p • w p

  -- Alternative notation for _•_
  mm : ⟦ C ⟧ S → S
  mm (s , v) = s • v

private
  cong-apply : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    → (f : A → C) (g : B → C) {h : A → B} → (f ≗ g ∘′ h)
    → {x : A} {y : B} → (h x ≡ y)
    → f x ≡ g y
  cong-apply f g f≗gh {x = x} hx≡y = ≡.trans (f≗gh x) (≡.cong g hx≡y)

  dsubst₂-∘₂ : ∀ {a b c ℓ}
    {A : Set a} {B : A → Set b} {C : Set c} (P : C → Set ℓ)
    {f : (x : A) → (y : B x) → C}
    {x x' y y'} (eq₁ : x ≡ x') (eq₂ : ≡.subst B eq₁ y ≡ y')
    {p : P (f x y)}
     → ≡.dsubst₂ (P F.∘₂ f) eq₁ eq₂ p ≡ ≡.subst P (≡.dcong₂ f eq₁ eq₂) p
  dsubst₂-∘₂ _ ≡.refl ≡.refl = ≡.refl
  
  dsubst₂-uncurry : ∀ {a b ℓ}
    {A : Set a} {B : A → Set b}
    → (P : (x : A) → (y : B x) → Set ℓ)
    → {x x' : A} (eq₁ : x ≡ x')
    → {y : B x} {y' : B x'} (eq₂ : ≡.subst B eq₁ y ≡ y')
    → (let eq = ProdProp.Σ-≡,≡→≡ (eq₁ , eq₂))
    → {p : P x y}
    → ≡.dsubst₂ P eq₁ eq₂ p ≡ ≡.subst (Prod.uncurry P) eq p
  dsubst₂-uncurry _ ≡.refl ≡.refl = ≡.refl

  dcong₂-uncurry : ∀ {a b ℓ}
    {A : Set a} {B : A → Set b} {C : Set ℓ}
    → (f : (x : A) → (y : B x) → C)
    → {x x' : A} (eq₁ : x ≡ x')
    → {y : B x} {y' : B x'} (eq₂ : ≡.subst B eq₁ y ≡ y')
    → (let eq = ProdProp.Σ-≡,≡→≡ (eq₁ , eq₂))
    → ≡.dcong₂ f eq₁ eq₂ ≡ ≡.cong (Prod.uncurry f) eq
  dcong₂-uncurry _ ≡.refl ≡.refl = ≡.refl

module EqualityDefinition (C : Container s p) where
  open import Relation.Binary using (Rel; IsEquivalence)
  open Container C renaming (Shape to S; Position to P)
  import Data.Container.Relation.Binary.Equality.Setoid as CEq
  open import Data.Container.Relation.Binary.Pointwise
    using (Pointwise)
    renaming (_,_ to mkEq)
    public

  Eq : Rel (⟦ C ⟧ S) _
  Eq = CEq.Eq (≡.setoid S) C

  shapeEq : ∀ {cx cy} → Eq cx cy → proj₁ cx ≡ proj₁ cy
  shapeEq = Pointwise.shape

  positionEq : ∀ {cx cy : ⟦ C ⟧ S} → (eq : Eq cx cy) → proj₂ cx ≗ proj₂ cy ∘′ ≡.subst P (shapeEq eq)
  positionEq = Pointwise.position

  instance
    Eq-isEquivalence : IsEquivalence Eq
    Eq-isEquivalence = CEq.isEquivalence (≡.setoid S) C

record IsMonad (C : Container s p) (raw : RawMonad C) : Set (s ⊔ p) where
  open RawMonad raw
  open EqualityDefinition C public

  field
    •-cong : ∀ {cx cy : ⟦ C ⟧ S}
      → Eq cx cy → mm cx ≡ mm cy
    ↖-cong : ∀ {cx cy : ⟦ C ⟧ S}
      → (eq : Eq cx cy)
      → ∀ (p : P (mm cx)) → ≡.subst P (shapeEq eq) (↖ p) ≡ ↖ (≡.subst P (•-cong eq) p)
    ↗-cong : ∀ {cx cy : ⟦ C ⟧ S}
      → (eq : Eq cx cy)
      → ∀ (p : P (mm cx))
      → ≡.subst P (cong-apply (proj₂ cx) (proj₂ cy) (positionEq eq) (↖-cong eq p)) (↗ p)
          ≡
        ↗ (≡.subst P (•-cong eq) p)

    •-ε : ∀ (s : S) → s • F.const ε ≡ s
    ε-• : ∀ (s : S) → ε • F.const s ≡ s
    •-• : ∀ (s : S) (v : P s → S) (w : (p : P s) → P (v p) → S)
      → (s • v) • diag w ≡ s • zip v w
    
    ↖-inner-ε : ∀ {s : S} (p : P (s • F.const ε))
      → ↖ p ≡ ≡.subst P (•-ε s) p
    ↗-outer-ε : ∀ {s : S} (p : P (ε • F.const s))
      → ↗ p ≡ ≡.subst P (ε-• s) p
    
    ↖-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
      → {p : P ((s • v) • diag w)} {q : P (s • zip v w)}
      → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
      → ↖ (↖ p) ≡ ↖ q
    ↗-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
      → {p : P ((s • v) • diag w)} {q : P (s • zip v w)}
      → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
      → (let p₁₁≡q₁ = ↖-↖ p≡q)
      → ≡.subst (λ r → P (v r)) p₁₁≡q₁ (↗ (↖ p)) ≡ ↖ (↗ q)
    ↗-↗ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
      → {p : P ((s • v) • diag w)} {q : P (s • zip v w)}
      → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
      → (let p₁₁≡q₁ = ↖-↖ p≡q)
          (let p₁₂≡q₂₁ = ↗-↖ p≡q)
      → ≡.dsubst₂ (λ r₁ r₂ → P (w r₁ r₂)) p₁₁≡q₁ p₁₂≡q₂₁ (↗ p) ≡ ↗ (↗ q)

module ≡-util {a b c ℓ : Level} where
  subst-dcong₂ : ∀ {A : Set a} {B : A → Set b} {C : Set c}
    → (P : C → Set ℓ)
    → (f : (a₀ : A) → B a₀ → C)
    → {a₁ a₂ : A} (eqA : a₁ ≡ a₂) {b₁ : B a₁} {b₂ : B a₂} (eqB : ≡.subst B eqA b₁ ≡ b₂)
    → ≡.subst P (≡.dcong₂ f eqA eqB) ≡ ≡.dsubst₂ (λ a b → P (f a b)) eqA eqB
  subst-dcong₂ P f ≡.refl ≡.refl = ≡.refl

module _ {C : Container s p} where

  -- Uustalu-style can be thought of as the _unpacked_
  -- version of Container.Algebra.Monad; hence
  -- the conversions between two are named `pack` and `unpack`.

  pack : RawMonad C → MM.RawMonad C
  pack raw' = record{ unit = unit; join = join }
    where
      open RawMonad raw'

      unit : Id ⇒ C
      unit = F.const ε ▷ F.const tt

      join : Comp C C ⇒ C
      join .shape (s , v) = s • v
      join .position {s = s , v} p = mk◇ (↖ p , ↗ p)

  open import Container.Effect.Functor.Lax using (mkLaxEq; toEq; fromEq)

  packWellDefined : (raw' : RawMonad C)
    → IsMonad C raw' → MM.WellDefinedJoin (pack raw')
  packWellDefined raw' isMonad' = record{
      shape-cong = λ x∼y → •-cong (toEq x∼y);
      position-cong = λ {x} {y} {p} x∼y@(mkLaxEq shapeEq posEq) →
        ◇-dcong P (↖-cong (toEq x∼y) p)
          (≡.trans
            (≡.trans
              (≡.subst-∘ {P = P} (↖-cong (toEq x∼y) p))
              (≡.subst-subst {P = P} (posEq (↖ p))))
            (↗-cong (toEq x∼y) p)
          )
    }
    where
      open RawMonad raw'
      open IsMonad isMonad'
      open Compose.◇-util using (◇-dcong)

  packLaw : (raw' : RawMonad C)
    → IsMonad C raw' → MM.IsMonad C (pack raw')
  packLaw raw' isMonad' = record{ impl }
    where
      module impl where
        open Compose.◇-util using (curry◇; ◇-dcong; ◇-assocˡ)
        
        open RawMonad raw'
        open IsMonad isMonad'
        open MM.RawMonad (pack raw') hiding (S; P)

        left-unit = mk≈ ε-• (λ _ p → ↗-outer-ε p)
        right-unit = mk≈ •-ε (λ _ p → ↖-inner-ε p)

        private
          j : ⟦ C ⟧ S → S
          j = Prod.uncurry _•_
          
          assoc-shape : (s₃ : ⟦ Comp C C ⟧ S) →
            j (⟪ join ⟫ s₃) ≡ j (map⟦⟧ j (Compose.from-Comp C C s₃))
          assoc-shape ( (s , v) , w◇ ) = •-• s v (curry◇ w◇)

          assoc-pos : (s₃ : ⟦ Comp C C ⟧ S) (p : P (j (⟪ join ⟫ s₃)))
            → (let q = ≡.subst P (assoc-shape s₃) p)
            → mk◇ (mk◇ (↖ (↖ p) , ↗ (↖ p)) , ↗ p)
                ≡
              ◇-assocˡ (mk◇ (↖ q , mk◇ (↖ (↗ q), ↗ (↗ q))))
          assoc-pos s₃@(_ , w◇) p = ◇-dcong P (◇-dcong P eqLL eqRL) eqRR'
            where
              q = ≡.subst P (assoc-shape s₃) p
              p≡q = ≡.refl {x = q}
              w = curry◇ w◇

              eqLL = ↖-↖ p≡q
              eqRL = ↗-↖ p≡q
              eqRR = ↗-↗ p≡q

              same-subst : _ ≡ ≡.dsubst₂ (λ p₁ p₂ → P (w p₁ p₂)) eqLL eqRL
              same-subst =
                ≡-util.subst-dcong₂
                  (λ p' → P (w◇ p'))
                  (λ p₁ p₂ → mk◇ (p₁ , p₂))
                  eqLL
                  eqRL
              eqRR' = ≡.trans (≡.cong-app same-subst (↗ p)) eqRR

        assoc = mk≈ assoc-shape assoc-pos

  unpack : MM.RawMonad C → RawMonad C
  unpack raw = record {rawMonadImpl'}
    where
      module rawMonadImpl' where
        open MM.RawMonad raw

        ε : S
        ε = shape unit tt

        _•_ : (s : S) → (P s → S) → S
        _•_ s v = shape join (s , v)

        ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
        ↖ {s} {v} p = proj₁ (◇.proof (position join { s = s , v } p))

        ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))
        ↗ {s} {v} p = proj₂ (◇.proof (position join {s = s , v } p))

  unpackLaw : (raw : MM.RawMonad C) →
    MM.IsMonad C raw → MM.WellDefinedJoin raw → IsMonad C (unpack raw)
  unpackLaw raw isMonad join-well = record {impl} where
    module impl where
      open EqualityDefinition C
      open Compose.◇-util

      open MM.RawMonad raw hiding (S; P)
      open RawMonad (unpack raw)
      open MM.IsMonad isMonad
      open Lax.WellDefined join-well
      module LCC = Lax.LaxContainer (LaxComp.laxComp C C)

      •-cong : ∀ {cx cy : ⟦ C ⟧ S}
        → Eq cx cy → mm cx ≡ mm cy
      •-cong cx∼cy = shape-cong (fromEq cx∼cy)

      ↖-cong : ∀ {cx cy : ⟦ C ⟧ S}
        → (eq : Eq cx cy)
        → ∀ (p : P (mm cx)) → ≡.subst P (shapeEq eq) (↖ p) ≡ ↖ (≡.subst P (•-cong eq) p)
      ↖-cong eq p = ◇-injectiveˡ (position-cong (fromEq eq))
      
      ↗-cong : ∀ {cx cy : ⟦ C ⟧ S}
        → (eq : Eq cx cy)
        → ∀ (p : P (mm cx))
        → ≡.subst P (cong-apply (proj₂ cx) (proj₂ cy) (positionEq eq) (↖-cong eq p)) (↗ p)
            ≡
          ↗ (≡.subst P (•-cong eq) p)
      ↗-cong {cx} {cy} eq p = begin
          ≡.subst P (cong-apply (proj₂ cx) (proj₂ cy) (positionEq eq) (↖-cong eq p)) (↗ p)
        ≡⟨⟩
          ≡.subst P (≡.trans (positionEq eq (↖ p)) (≡.cong (proj₂ cy) (↖-cong eq p)))
            (↗ p)
        ≡⟨ ≡.subst-subst (positionEq eq (↖ p)) ⟨
          ≡.subst P (≡.cong (proj₂ cy) (↖-cong eq p))
            (≡.subst P (positionEq eq (↖ p)) (↗ p))
        ≡⟨ ≡.subst-∘ (↖-cong eq p) ⟨
          ≡.subst (P F.∘ proj₂ cy) (↖-cong eq p)
            (≡.subst P (positionEq eq (↖ p)) (↗ p))
        ≡⟨ ◇-injectiveʳ (position-cong (fromEq eq)) ⟩
          ↗ (≡.subst P (•-cong eq) p)
        ∎
        where
          open ≡.≡-Reasoning

      •-ε : ∀ (s : S) → s • F.const ε ≡ s
      •-ε s = right-unit ._≈_.shape s

      ε-• : ∀ (s : S) → ε • F.const s ≡ s
      ε-• s = left-unit ._≈_.shape s
      
      •-• : ∀ (s : S) (v : P s → S) (w : (p : P s) → P (v p) → S)
        → (s • v) • diag w ≡ s • zip v w
      •-• s v w = assoc ._≈_.shape ((s , v) , uncurry◇ w)
      
      ↖-inner-ε : ∀ {s : S} (p : P (s • F.const ε))
        → ↖ p ≡ ≡.subst P (•-ε s) p
      ↖-inner-ε {s = s} p = right-unit ._≈_.position s p

      ↗-outer-ε : ∀ {s : S} (p : P (ε • F.const s))
        → ↗ p ≡ ≡.subst P (ε-• s) p
      ↗-outer-ε {s = s} p = left-unit ._≈_.position s p

      module _
          {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
           where
        svw : ⟦ Comp C C ⟧ S
        svw = (s , v) , uncurry◇ w
        
        svw' : ⟦ C ⟧ (⟦ C ⟧ S)
        svw' = s , λ p → (v p , w p)

        ppp : P ((s • v) • diag w) → ◇ (Comp C C) P svw
        ppp p = mk◇ (mk◇ (↖ (↖ p) , ↗ (↖ p)) , ↗ p)
        
        qqq : P (s • zip v w) → ◇ C (◇ C P) svw'
        qqq q = mk◇ (↖ q , mk◇ (↖ (↗ q) , ↗ (↗ q)))

        assoc-pos : (p : P ((s • v) • diag w)) → ppp p ≡ ◇-assocˡ (qqq (≡.subst P (•-• s v w) p))
        assoc-pos p = assoc ._≈_.position svw p

        ↖-↖ : ∀ {p : P ((s • v) • diag w)} {q : P (s • zip v w)}
          → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
          → ↖ (↖ p) ≡ ↖ q
        ↖-↖ {p = p} ≡.refl = ◇-injectiveˡ (◇-injectiveˡ (assoc-pos p))

        ↗-↖ : ∀ {p : P ((s • v) • diag w)} {q : P (s • zip v w)}
          → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
          → (let p₁₁≡q₁ = ↖-↖ p≡q)
          → ≡.subst (λ r → P (v r)) p₁₁≡q₁ (↗ (↖ p)) ≡ ↖ (↗ q)
        ↗-↖ {p = p} ≡.refl = ◇-injectiveʳ (◇-injectiveˡ (assoc-pos p))
        
        w◇ : ◇ C P (s , v) → S
        w◇ = uncurry◇ w

        dcong₂-uncurry◇ : ∀ {p₁ q₁ : P s}
          → (eq₁ : p₁ ≡ q₁)
          → {p₂ : P (v p₁)} {q₂ : P (v q₁)}
          → (eq₂ : ≡.subst (P F.∘ v) eq₁ p₂ ≡ q₂)
          → ≡.dcong₂ w eq₁ eq₂ ≡ ≡.cong w◇ (◇-dcong P {cx = s , v} eq₁ eq₂)
        dcong₂-uncurry◇ ≡.refl ≡.refl = ≡.refl

        ↗-↗ : ∀ {p : P ((s • v) • diag w)} {q : P (s • zip v w)}
          → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
          → (let p₁₁≡q₁ = ↖-↖ p≡q) (let p₁₂≡q₂₁ = ↗-↖ p≡q)
          → ≡.dsubst₂ (P F.∘₂ w) p₁₁≡q₁ p₁₂≡q₂₁ (↗ p) ≡ ↗ (↗ q)
        ↗-↗ {p = p} {q = q} ≡.refl =
          begin
            ≡.dsubst₂ (P F.∘₂ w) eq₁ eq₂ (↗ p)
          ≡⟨ dsubst₂-∘₂ P eq₁ eq₂ ⟩
            ≡.subst P (≡.dcong₂ w eq₁ eq₂) (↗ p)
          ≡⟨ ≡.cong (λ e → ≡.subst P e (↗ p)) (dcong₂-uncurry◇ eq₁ eq₂) ⟩
            ≡.subst P (≡.cong w◇ eq◇) (↗ p)
          ≡⟨ ≡.subst-∘ eq◇ ⟨
            ≡.subst (P F.∘ w◇) eq◇ (↗ p)
          ≡⟨ ≡.cong (λ e → ≡.subst (P F.∘ w◇) e (↗ p)) eq◇≡assoc-posˡ ⟩
            ≡.subst (P F.∘ w◇) (◇-injectiveˡ (assoc-pos p))
              (↗ p)
          ≡⟨ ◇-injectiveʳ (assoc-pos p) ⟩
            ↗ (↗ q)
          ∎
          where
            eq₁ : ↖ (↖ p) ≡ ↖ q
            eq₁ = ↖-↖ ≡.refl
            
            eq₂ : ≡.subst (P F.∘ v) eq₁ (↗ (↖ p)) ≡ ↖ (↗ q)
            eq₂ = ↗-↖ ≡.refl

            eq◇ : mk◇ (↖ (↖ p) , ↗ (↖ p)) ≡ mk◇ (↖ q , ↖ (↗ q))
            eq◇ = ◇-dcong P eq₁ eq₂

            eq◇≡assoc-posˡ : eq◇ ≡ ◇-injectiveˡ (assoc-pos p)
            eq◇≡assoc-posˡ = ◇-dcong-split P (◇-injectiveˡ (assoc-pos p))

            open ≡.≡-Reasoning

module _ {c c'} {C₁ C₂ : Container c c'}
  (iso : C₁ ⇔ C₂) where
  open _⇔_ iso

  transferRawMonad : RawMonad C₁ → RawMonad C₂
  transferRawMonad raw = unpack (MM.transferRawMonad iso (pack raw))
  
  transferIsMonad : ∀ {raw : RawMonad C₁}
    → IsMonad C₁ raw → IsMonad C₂ (transferRawMonad raw)
  transferIsMonad {raw = raw} law₁ = unpackLaw _ isMonad₂ well₂
    where
      rawMonad₁ = pack raw
      rawMonad₂ = MM.transferRawMonad iso rawMonad₁
      well₁ = packWellDefined raw law₁
      well₂ = MM.transferWell iso {rawC = rawMonad₁} well₁
      isMonad₁ = packLaw raw law₁
      isMonad₂ = MM.transferIsMonad iso isMonad₁ well₁
