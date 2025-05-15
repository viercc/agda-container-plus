{-# OPTIONS --without-K --safe #-}

module Container.Combinator.Monoidal where

open import Level

open import Data.Container.Core
open import Data.Container.Morphism using (id; _∘_)
open import Container.Morphism.Equality using (_≈_; mk≈)
open import Container.Morphism.Iso

private
  variable
    c c' d d' e e' f f' : Level

module _ (H : Container c c' → Container d d') where
  Map : Set (suc (c ⊔ c') ⊔ d ⊔ d')
  Map = ∀ {C₁ C₂ : Container c c'} → (C₁ ⇒ C₂) → (H C₁ ⇒ H C₂)

  record Functorial (map : Map) : Set (suc (c ⊔ c') ⊔ d ⊔ d') where
    constructor mkFunctorial
    field
      map-id : ∀ {C₁ : Container c c'} → map (id C₁) ≈ id (H C₁)
      
      map-∘ : ∀ {C₁ C₂ C₃ : Container c c'}
        → (α : C₂ ⇒ C₃) → (β : C₁ ⇒ C₂) → map (α ∘ β) ≈ map α ∘ map β  

module _ (H : Container c c' → Container d d' → Container e e') where
  Map₁ : Set (suc (c ⊔ c' ⊔ d ⊔ d') ⊔ e ⊔ e')
  Map₁ = ∀ {D : Container d d'} → Map (λ C → H C D)

  Map₂ : Set (suc (c ⊔ c' ⊔ d ⊔ d') ⊔ e ⊔ e')
  Map₂ = ∀ {C : Container c c'} → Map (H C)

  record Bifunctorial (map₁ : Map₁) (map₂ : Map₂) : Set (suc (c ⊔ c' ⊔ d ⊔ d') ⊔ e ⊔ e') where
    constructor mkFunctorial
    field
      functorial₁ : ∀ {D} → Functorial (λ C → H C D) map₁
      functorial₂ : ∀ {C} → Functorial (H C) map₂
      map₁-map₂ : ∀ {C₁ C₂ D₁ D₂}
        → (α : C₁ ⇒ C₂) → (β : D₁ ⇒ D₂) → map₁ α ∘ map₂ β ≈ map₂ β ∘ map₁ α
    
    bimap : ∀ {C₁ C₂ D₁ D₂} → (C₁ ⇒ C₂) → (D₁ ⇒ D₂) → H C₁ D₁ ⇒ H C₂ D₂
    bimap α β = map₁ α ∘ map₂ β

    open module functorial₁ {D : Container d d'} = Functorial (functorial₁ {D})
      renaming (map-id to map₁-id; map-∘ to map₁-∘) public
    open module functorial₂ {C : Container c c'} = Functorial (functorial₂ {C})
      renaming (map-id to map₂-id; map-∘ to map₂-∘) public

module _ (H : Container c c' → Container c c' → Container c c') where
  Assoc : Set (suc (c ⊔ c'))
  Assoc = ∀ {C D E : Container c c'}
    → H (H C D) E ⇔ H C (H D E)
  
  record Semigroupal (map₁ : Map₁ H) (map₂ : Map₂ H) (assoc⇔ : Assoc) : Set (suc (c ⊔ c')) where
    constructor mkAssociative

    assocʳ : ∀ {C D E : Container c c'} → H (H C D) E ⇒ H C (H D E)
    assocʳ = assoc⇔ ._⇔_.to

    field
      bifunctorial : Bifunctorial H map₁ map₂
    
    open Bifunctorial bifunctorial public

    field
      assoc-nat : ∀ {C₁ C₂ D₁ D₂ E₁ E₂ : Container c c'} →
           (α : C₁ ⇒ C₂) (β : D₁ ⇒ D₂) (γ : E₁ ⇒ E₂)
        → bimap α (bimap β γ) ∘ assocʳ ≈ assocʳ ∘ bimap (bimap α β) γ
      pentagon : ∀ {C D E F} →
        assocʳ {C} {D} {H E F} ∘ assocʳ {H C D} {E} {F} ≈ map₂ assocʳ ∘ assocʳ ∘ map₁ assocʳ

module _ (H : Container c c' → Container c c' → Container c c') (Id : Container c c') where
  UnitL : Set (suc (c ⊔ c'))
  UnitL = ∀ {C : Container c c'} → H Id C ⇔ C

  UnitR : Set (suc (c ⊔ c'))
  UnitR = ∀ {C : Container c c'} → H C Id ⇔ C

  open _⇔_ using (to)

  record Monoidal (map₁ : Map₁ H) (map₂ : Map₂ H) (assoc⇔ : Assoc H) (ul⇔ : UnitL) (ur⇔ : UnitR)
       : Set (suc (c ⊔ c'))
    where
      constructor mkMonoidal

      field
        semigroupal : Semigroupal H map₁ map₂ assoc⇔

      open Semigroupal semigroupal

      unitL : ∀ {C : Container c c'} → H Id C ⇒ C
      unitL = ul⇔ .to
      
      unitR : ∀ {C : Container c c'} → H C Id ⇒ C
      unitR = ur⇔ .to

      field
        unitl-nat : ∀ {C₁ C₂} (α : C₁ ⇒ C₂) → α ∘ unitL ≈ unitL ∘ map₂ α
        unitr-nat : ∀ {C₁ C₂} (α : C₁ ⇒ C₂) → α ∘ unitR ≈ unitR ∘ map₁ α

        unit-unit : unitL {C = Id} ≈ unitR {C = Id}
        assoc-unit : ∀ {C D} →
          map₂ unitL ∘ assocʳ {C = C} {D = Id} {E = D} ≈ map₁ unitR