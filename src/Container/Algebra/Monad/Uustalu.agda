{-# OPTIONS --without-K --safe #-}

module Container.Algebra.Monad.Uustalu where

open import Level

import Function as F
import Data.Product as Prod
open Prod using (proj₁; proj₂; _,_)
open import Data.Unit.Polymorphic.Base using (⊤; tt)

open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_; _≗_)

open import Data.Container.Core renaming (map to map⟦⟧)
import Data.Container.Relation.Unary.Any as C◇
open C◇ using (◇) renaming (any to mk◇)

open import Data.Container.Morphism using (id; _∘_)
import Data.Container.Combinator as CC

open import Container.Morphism.Equality
open import Container.Morphism.Iso

import Container.Combinator.Compose.Properties as ∘-Properties
open ∘-Properties using (Id; Comp)

import Container.Algebra.Monad as MM

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
  
record IsMonad (C : Container s p) (raw : RawMonad C) : Set (s ⊔ p) where
  open RawMonad raw

  diag : ∀ {s : S} {v : P s → S} (w : (p₁ : P s) → P (v p₁) → S)
    → P (s • v) → S
  diag {s} {v} w p = w (↖ p) (↗ p)

  field
    •-ε : ∀ (s : S) → s • F.const ε ≡ s
    ε-• : ∀ (s : S) → ε • F.const s ≡ s
    •-• : ∀ (s : S) (v : P s → S) (w : (p : P s) → P (v p) → S)
      → (s • v) • diag w ≡ s • (λ p → v p • w p)
    
    ↖-inner-ε : ∀ {s : S} (p : P (s • F.const ε))
      → ↖ p ≡ ≡.subst P (•-ε s) p
    ↗-outer-ε : ∀ {s : S} (p : P (ε • F.const s))
      → ↗ p ≡ ≡.subst P (ε-• s) p
    
    ↖-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
      → {p : P ((s • v) • diag w)} {q : P (s • (λ q₁ → v q₁ • w q₁))}
      → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
      → ↖ (↖ p) ≡ ↖ q
    ↗-↖ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
      → {p : P ((s • v) • diag w)} {q : P (s • (λ q₁ → v q₁ • w q₁))}
      → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
      → (let p₁₁≡q₁ = ↖-↖ p≡q)
      → ≡.subst (λ r → P (v r)) p₁₁≡q₁ (↗ (↖ p)) ≡ ↖ (↗ q)
    ↗-↗ : ∀ {s : S} {v : P s → S} {w : (p : P s) → P (v p) → S}
      → {p : P ((s • v) • diag w)} {q : P (s • (λ q₁ → v q₁ • w q₁))}
      → (p≡q : ≡.subst P (•-• s v w) p ≡ q)
      → (let p₁₁≡q₁ = ↖-↖ p≡q)
          (let p₁₂≡q₂₁ = ↗-↖ p≡q)
      → ≡.dsubst₂ (λ r₁ r₂ → P (w r₁ r₂)) p₁₁≡q₁ p₁₂≡q₂₁ (↗ p) ≡ ↗ (↗ q)

from-Uustalu : ∀ {C : Container s p} (rawMonad' : RawMonad C) → MM.RawMonad C
from-Uustalu {C = C} rawMonad' = record{ unit = unit; join = join }
  where
    open RawMonad rawMonad'

    unit : Id ⇒ C
    unit = F.const ε ▷ F.const tt

    join : Comp C C ⇒ C
    join .shape (s , v) = s • v
    join .position {s = s , v} p = mk◇ (↖ p , ↗ p)

module ≡-util {a b c ℓ : Level} where
  subst-dcong₂ : ∀ {A : Set a} {B : A → Set b} {C : Set c}
    → (P : C → Set ℓ)
    → (f : (a₀ : A) → B a₀ → C)
    → {a₁ a₂ : A} (eqA : a₁ ≡ a₂) {b₁ : B a₁} {b₂ : B a₂} (eqB : ≡.subst B eqA b₁ ≡ b₂)
    → ≡.subst P (≡.dcong₂ f eqA eqB) ≡ ≡.dsubst₂ (λ a b → P (f a b)) eqA eqB
  subst-dcong₂ P f ≡.refl ≡.refl = ≡.refl

from-Uustalu-law : ∀ {C : Container s p} (raw' : RawMonad C) (isMonad' : IsMonad C raw')
  → MM.IsMonad C (from-Uustalu raw')
from-Uustalu-law {C = C} raw' isMonad' = record{ impl }
  where
    module impl where
      open ∘-Properties using (map₁; map₂)
      open ∘-Properties.◇-util using (curry◇; ◇-dcong; ◇-assocˡ)
      
      open RawMonad raw'
      open IsMonad isMonad'
      open MM.RawMonad (from-Uustalu raw') hiding (S; P)

      left-unit = mk≈ ε-• (λ _ p → ↗-outer-ε p)
      right-unit = mk≈ •-ε (λ _ p → ↖-inner-ε p)

      private
        j : ⟦ C ⟧ S → S
        j = Prod.uncurry _•_
        
        assoc-shape : (s₃ : ⟦ Comp C C ⟧ S) →
          j (⟪ join ⟫ s₃) ≡ j (map⟦⟧ j (CC.from-∘ C C s₃))
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

to-Uustalu : ∀ {C : Container s p} (rawMonad : MM.RawMonad C) → RawMonad C
to-Uustalu rawMonad = record {rawMonadImpl'}
  where
    module rawMonadImpl' where
      open MM.RawMonad rawMonad

      ε : S
      ε = shape unit tt

      _•_ : (s : S) → (P s → S) → S
      _•_ s v = shape join (s , v)

      ↖ : {s : S} → {v : P s → S} → P (s • v) → P s
      ↖ {s} {v} p = proj₁ (◇.proof (position join { s = s , v } p))

      ↗ : {s : S} → {v : P s → S} → (p : P (s • v)) → P (v (↖ p))
      ↗ {s} {v} p = proj₂ (◇.proof (position join {s = s , v } p))
 
-- TODO: to-Uustalu-law