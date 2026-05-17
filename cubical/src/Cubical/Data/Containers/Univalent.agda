{-# OPTIONS --safe --cubical --guardedness #-}
module Cubical.Data.Containers.Univalent where

open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Data.Sigma
import Cubical.Foundations.Isomorphism as TypeIso
open TypeIso using (Iso; iso)
open import Cubical.Foundations.GroupoidLaws
  using (lCancel)
open import Cubical.Foundations.Transport
  using (substComposite; substCommSlice)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Data.Containers.Base as C

private
  variable
    ℓ ℓ' : Level

-- Pointwise isomorphisms imply isomorphism between Π
ΠIso→IsoΠ : ∀ {ℓx ℓy : Level}
  {X : Type ℓx}
  {P Q : X → Type ℓy}
  → (∀ x → Iso (P x) (Q x))
  → Iso (∀ x → P x) (∀ x → Q x)
ΠIso→IsoΠ φ =
  iso
    (λ px x → Iso.fun (φ x) (px x))
    (λ qx x → Iso.inv (φ x) (qx x))
    (λ px → funExt (λ x → Iso.rightInv (φ x) (px x)))
    (λ qx → funExt (λ x → Iso.leftInv (φ x) (qx x)))

module Category-subst-props
  {ℓ ℓ' : Level}
  (𝒞 : Category ℓ ℓ') where

  open Category 𝒞

  id[_] : {A B : ob} → A ≡ B → Hom[ A , B ]
  id[_] {A} {B} eq = subst Hom[ A ,_] eq id
  -- NB: this exists as `pathToMorphism` in the latest `cubical` lib
  -- (but not in the version I'm using)

  id-refl : {A : ob} → id[ refl {x = A} ] ≡ id
  id-refl {A} = transportRefl id

  id-sym : {A B : ob} → (eq : A ≡ B)
    → subst Hom[_, A ] eq id ≡ id[ sym eq ]
  id-sym {A} =
    J (λ _ p → subst Hom[_, A ] p id ≡ id[ sym p ]) refl

  subst-⋆-right : {A B X Y : ob} → (eq : A ≡ B)
    → (h1 : Hom[ X , Y ])
    → (h2 : Hom[ Y , A ])
    → subst Hom[ X ,_] eq (h1 ⋆ h2) ≡ h1 ⋆ subst Hom[ Y ,_] eq h2
  subst-⋆-right {A} {B} {X} {Y} eq h1 h2 =
    substCommSlice Hom[ Y ,_] Hom[ X ,_] (λ _ → h1 ⋆_) eq h2

  subst-⋆-left : {A B X Y : ob} → (eq : A ≡ B)
    → (h1 : Hom[ A , X ])
    → (h2 : Hom[ X , Y ])
    → subst Hom[_, Y ] eq (h1 ⋆ h2) ≡ subst Hom[_, X ] eq h1 ⋆ h2
  subst-⋆-left {A} {B} {X} {Y} eq h1 h2 =
    substCommSlice Hom[_, X ] Hom[_, Y ] (λ _ → _⋆ h2) eq h1

  subst-Hom-right : {A B X : ob} → (eq : A ≡ B) → (h : Hom[ X , A ])
    → subst Hom[ X ,_] eq h ≡ h ⋆ id[ eq ]
  subst-Hom-right {A} {B} {X} eq h =
      subst Hom[ X ,_] eq h
    ≡⟨ cong (subst Hom[ X ,_] eq) (sym (⋆IdR h)) ⟩
      subst Hom[ X ,_] eq (h ⋆ id)
    ≡⟨ subst-⋆-right eq h id ⟩
      h ⋆ subst Hom[ A ,_] eq id
    ≡⟨⟩
      h ⋆ id[ eq ]
    ∎

  subst-Hom-left : {A B Y : ob} → (eq : A ≡ B) → (h : Hom[ A , Y ])
    → subst Hom[_, Y ] eq h ≡ id[ sym eq ] ⋆ h
  subst-Hom-left {A} {B} {Y} eq h =
      subst Hom[_, Y ] eq h
    ≡⟨ cong (subst Hom[_, Y ] eq) (sym (⋆IdL h)) ⟩
      subst Hom[_, Y ] eq (id ⋆ h)
    ≡⟨ subst-⋆-left eq id h ⟩
      subst Hom[_, A ] eq id ⋆ h
    ≡⟨ cong (_⋆ h) (id-sym eq) ⟩
      id[ sym eq ] ⋆ h
    ∎

  id-∙ : {A B C : ob} → (p : A ≡ B) (q : B ≡ C)
    → id[ p ∙ q ] ≡ id[ p ] ⋆ id[ q ] 
  id-∙ {A} p q =
      id[ p ∙ q ]
    ≡⟨⟩
      subst Hom[ A ,_] (p ∙ q) id
    ≡⟨ substComposite Hom[ A ,_] p q id ⟩
      subst Hom[ A ,_] q (subst Hom[ A ,_] p id)
    ≡⟨ subst-Hom-right q (id[ p ]) ⟩
      subst Hom[ A ,_] p id ⋆ id[ q ]
    ≡⟨⟩
      id[ p ] ⋆ id[ q ]
    ∎
  
  id-lCancel : {A B : ob} → (p : A ≡ B)
    → id[ sym p ] ⋆ id[ p ] ≡ id
  id-lCancel p = sym (id-∙ (sym p) p) ∙ cong id[_] (lCancel p) ∙ id-refl

  subst-Hom-nat : ∀ {ℓ'' : Level} { S : Type ℓ'' } { a b : S } (eq : a ≡ b)
    → ∀ {F G : S → ob} (p : ∀ s → Hom[ F s , G s ])
    → p a ⋆ id[ cong G eq ] ≡ id[ cong F eq ] ⋆ p b 
  subst-Hom-nat {a = a} {b = b} eq {F = F} {G = G} p = _

-- Converts between paths on container morphisms ⇒c 
-- and "sigma paths"
module _ {ℓ ℓ' : Level}
  {ℬ : Category ℓ ℓ'} {C D : GenContainer ℬ} where
  open C.Conts ℬ
  open _⇒c_

  open GenContainer C
  open GenContainer D renaming (S to T; P to Q; isSetS to isSetT)

  Mor' : Type ℓ'
  Mor' = ∀ (s : S) → Σ[ t ∈ T ] (ℬ [ Q t , P s ])

  private
    unpack : (C ⇒c D) → Mor'
    unpack h s = h .shape s , h .pos s

    pack : Mor' → (C ⇒c D)
    pack h' .shape = λ s → h' s .fst
    pack h' .pos = λ s → h' s .snd

    -- check: definitionally unpack and pack are inverses
    _ : (∀ h → pack (unpack h) ≡ h) × (∀ h' → unpack (pack h') ≡ h')
    _ = (λ _ → refl) , (λ _ → refl)

  MorPathTransport : (f g : C ⇒c D)
    → Type ℓ'
  MorPathTransport f g =
    ∀ s → ΣPathTransport (unpack f s) (unpack g s)
  -- = ∀ s → Σ[ eqS ∈ f .shape s ≡ g .shape s ]
  --    (transport (λ i → ℬ [ Q (eqS i) , P s ]) (f .pos s) ≡ g .pos s)

  Iso-MorPathTransport :
    ∀{f g : C ⇒c D} → Iso (MorPathTransport f g) (f ≡ g)
  Iso-MorPathTransport {f} {g} =
      TypeIso.compIso
        (ΠIso→IsoΠ (λ s → IsoΣPathTransportPathΣ (unpack f s) (unpack g s)))
        iso-unpack-ext
    where
      iso-unpack-ext : Iso (∀ s → unpack f s ≡ unpack g s) (f ≡ g)
      iso-unpack-ext = iso
        (λ eq → cong pack (funExt eq))
        (λ eq → funExt⁻ (cong unpack eq)) (λ _ → refl) (λ _ → refl)

module _ {ℓ ℓ' : Level} {ℬ : Category ℓ ℓ'} where
  Container : Type _
  Container = GenContainer ℬ

  open Category ℬ
  open Category-subst-props ℬ
  open C.Conts ℬ
  open _⇒c_

  private
    Container' : Type (ℓ-max ℓ (ℓ-suc ℓ'))
    Container' = Σ (Σ[ S ∈ Type ℓ' ] (S → ob)) (λ r → isSet (fst r))

    Container→Σ : Container → Container'
    Container→Σ (S ◁ P & isSetS) = (S , P) , isSetS

    Σ→Container : Container' → Container
    Σ→Container ((S , P) , isSetS) = (S ◁ P & isSetS)

    Container↔Σ : Iso Container Container'
    Container↔Σ = iso Container→Σ Σ→Container (λ _ → refl) (λ _ → refl)

  ΣIsoIso : (C D : Container) → Type _
  ΣIsoIso (S ◁ P & _) (T ◁ Q & _) =
    Σ[ f ∈ Iso S T ] (∀ s → CatIso ℬ (Q (Iso.fun f s)) (P s))

  module _ {C D : Container} where
    open GenContainer C
    open GenContainer D renaming (S to T; P to Q; isSetS to isSetT)

    ContIso→ΣIsoIso : CatIso Cont C D → ΣIsoIso C D
    ContIso→ΣIsoIso (f , isiso g fg≡id gf≡id) = shapeIso , posIso
      where
        open Iso
        f0 = f .shape
        f1 = f .pos
        g0 = g .shape
        g1 = g .pos

        shape-fg≡id : ∀ t → f0 (g0 t) ≡ t
        shape-fg≡id t = fst (Iso-MorPathTransport .inv fg≡id t)

        shape-gf≡id : ∀ s → g0 (f0 s) ≡ s
        shape-gf≡id s = fst (Iso-MorPathTransport .inv gf≡id s)
        
        pos-fg≡id : ∀ t →
          transport (λ i → Hom[ Q (shape-fg≡id t i) , Q t ]) 
            (f1 (g0 t) ⋆ g1 t) ≡ id
        pos-fg≡id t = snd (Iso-MorPathTransport .inv fg≡id t)

        pos-gf≡id : ∀ s →
          transport (λ i → Hom[ P (shape-gf≡id s i) , P s ]) 
            (g1 (f0 s) ⋆ f1 s) ≡ id
        pos-gf≡id s = snd (Iso-MorPathTransport .inv gf≡id s)

        shapeIso : Iso S T
        shapeIso = iso f0 g0 shape-fg≡id shape-gf≡id

        posIso : ∀ s → CatIso ℬ (Q (f0 s)) (P s)
        posIso s = x , isiso y' (y'x-subst ∙ pos-gf≡id s) (xy'≡x''y ∙ x''y-subst ∙ pos-fg≡id (f0 s))
          where
            eq1 : g0 (f0 s) ≡ s
            eq1 = shape-gf≡id s

            eq2 : f0 (g0 (f0 s)) ≡ f0 s
            eq2 = shape-fg≡id (f0 s)

            eq1' = sym eq1
            eq2' = sym eq2

            x : Hom[ Q (f0 s) , P s ]
            x = f1 s

            x' : Hom[ Q (f0 (g0 (f0 s))) , P (g0 (f0 s)) ]
            x' = f1 (g0 (f0 s))

            x'' : Hom[ Q (f0 s) , P (g0 (f0 s)) ]
            x'' = subst Hom[_, P (g0 (f0 s)) ] (cong Q eq2) x'

            y : Hom[ P (g0 (f0 s)) , Q (f0 s) ]
            y = g1 (f0 s)

            y' : Hom[ P s , Q (f0 s)]
            y' = subst Hom[_, Q (f0 s)] (cong P eq1) y

            y'x-subst : y' ⋆ x ≡ subst Hom[_, P s ] (cong P eq1) (y ⋆ x)
            y'x-subst = sym (subst-⋆-left (cong P eq1) y x)

            x''y-subst : x'' ⋆ y ≡ subst Hom[_, Q (f0 s) ] (cong Q eq2) (x' ⋆ y)
            x''y-subst = sym (subst-⋆-left (cong Q eq2) x' y)

            xy'≡x''y : x ⋆ y' ≡ x'' ⋆ y
            xy'≡x''y =
                x ⋆ y'
              ≡⟨⟩
                x ⋆ subst Hom[_, Q (f0 s)] (cong P eq1) y
              ≡⟨ cong (x ⋆_) (subst-Hom-left (cong P eq1) y) ⟩
                 x ⋆ (id[ cong P eq1' ] ⋆ y)
              ≡⟨ sym (⋆Assoc _ _ _) ⟩
                 (x ⋆ id[ cong P eq1' ]) ⋆ y
              ≡⟨ cong (_⋆ y) (subst-Hom-nat eq1' f1) ⟩
                 (id[ cong Q (cong f0 eq1') ] ⋆ x') ⋆ y
              ≡⟨ cong (λ eq → (id[ cong Q eq ] ⋆ x') ⋆ y)
                  (isSetT _ _ (cong f0 eq1') eq2') ⟩
                 (id[ cong Q eq2' ] ⋆ x') ⋆ y
              ≡⟨ cong (_⋆ g1 (f0 s)) (sym (subst-Hom-left (cong Q eq2) _)) ⟩
                  subst Hom[_, P (g0 (f0 s))] (cong Q eq2) x' ⋆ y
              ≡⟨⟩
                  x'' ⋆ y
              ∎

    ΣIsoIso→ContIso : ΣIsoIso C D → CatIso Cont C D
    ΣIsoIso→ContIso (shapeIso , posIso) = f , isiso g fg≡id gf≡id
      where
        open Iso shapeIso
          renaming (
            fun to f0;
            inv to g0;
            rightInv to shape-fg≡id;
            leftInv to shape-gf≡id
          )

        f1 : ∀ s → Hom[ Q (f0 s) , P s ]
        f1 s = posIso s .fst

        g1' : ∀ s → Hom[ P s , Q (f0 s) ]
        g1' s = posIso s .snd .isIso.inv

        pos-fg≡id : ∀ s → f1 s ⋆ g1' s ≡ id
        pos-fg≡id s = posIso s .snd .isIso.ret

        pos-gf≡id : ∀ s → g1' s ⋆ f1 s ≡ id
        pos-gf≡id s = posIso s .snd .isIso.sec

        g1 : ∀ t → Hom[ P (g0 t) , Q t ]
        g1 t = g1' (g0 t) ⋆ id[ cong Q (shape-fg≡id t) ]

        f : C ⇒c D
        f = f0 ◁ f1
        
        g : D ⇒c C
        g = g0 ◁ g1

        MorPathTransport-fg-id : MorPathTransport (g ⋆c f) id-c
        MorPathTransport-fg-id t = shapeEq , posEq
          where
            shapeEq : f0 (g0 t) ≡ t
            shapeEq = shape-fg≡id t

            q : Q (f0 (g0 t)) ≡ Q t
            q = cong Q shapeEq

            posEq : subst Hom[_, Q t ] q (f1 (g0 t) ⋆ g1 t)
              ≡ id
            posEq =
                subst Hom[_, Q t ] q (f1 (g0 t) ⋆ g1 t)
              ≡⟨ subst-Hom-left q (f1 (g0 t) ⋆ g1 t) ⟩
                id[ sym q ] ⋆ f1 (g0 t) ⋆ g1 t
              ≡⟨⟩
                id[ sym q ] ⋆ f1 (g0 t) ⋆ g1' (g0 t) ⋆ id[ q ]
              ≡⟨ cong (id[ sym q ] ⋆_) (sym (⋆Assoc _ _ _)) ⟩
                id[ sym q ] ⋆ (f1 (g0 t) ⋆ g1' (g0 t)) ⋆ id[ q ]
              ≡⟨ cong (λ h → id[ sym q ] ⋆ h ⋆ id[ q ]) (pos-fg≡id (g0 t)) ⟩
                id[ sym q ] ⋆ id ⋆ id[ q ]
              ≡⟨ cong (id[ sym q ] ⋆_) (⋆IdL id[ q ]) ⟩
                id[ sym q ] ⋆ id[ q ]
              ≡⟨ id-lCancel q ⟩
                id
              ∎
        
        MorPathTransport-gf-id : MorPathTransport (f ⋆c g) id-c
        MorPathTransport-gf-id s = shapeEq , posEq
          where
            shapeEq : g0 (f0 s) ≡ s
            shapeEq = shape-gf≡id s

            p : P (g0 (f0 s)) ≡ P s
            p = cong P shapeEq

            q : Q (f0 (g0 (f0 s))) ≡ Q (f0 s)
            q = cong Q (shape-fg≡id (f0 s))

            q' : Q (f0 (g0 (f0 s))) ≡ Q (f0 s)
            q' = cong (λ s → Q (f0 s)) shapeEq

            q≡q' : q ≡ q'
            q≡q' = cong (cong Q) (isSetT _ _ (shape-fg≡id (f0 s)) (cong f0 shapeEq))

            aux : g1 (f0 s) ≡ id[ p ] ⋆ g1' s
            aux =
                g1 (f0 s)
              ≡⟨⟩
                g1' (g0 (f0 s)) ⋆ id[ q ]
              ≡⟨ cong (λ r → g1' (g0 (f0 s)) ⋆ id[ r ]) q≡q' ⟩
                g1' (g0 (f0 s)) ⋆ id[ q' ]
              ≡⟨ subst-Hom-nat shapeEq g1' ⟩
                id[ cong P shapeEq ] ⋆ g1' s
              ≡⟨⟩
                id[ p ] ⋆ g1' s
              ∎

            posEq : subst Hom[_, P s ] p (g1 (f0 s) ⋆ f1 s) ≡ id
            posEq =
                subst Hom[_, P s ] p (g1 (f0 s) ⋆ f1 s)
              ≡⟨ subst-Hom-left p (g1 (f0 s) ⋆ f1 s) ⟩
                id[ sym p ] ⋆ g1 (f0 s) ⋆ f1 s
              ≡⟨ cong (λ h → id[ sym p ] ⋆ h ⋆ f1 s) aux ⟩
                id[ sym p ] ⋆ (id[ p ] ⋆ g1' s) ⋆ f1 s
              ≡⟨ cong (id[ sym p ] ⋆_) (⋆Assoc _ _ _) ∙ sym (⋆Assoc _ _ _) ⟩
                (id[ sym p ] ⋆ id[ p ]) ⋆ (g1' s ⋆ f1 s)
              ≡⟨ cong₂ _⋆_ (id-lCancel p) (pos-gf≡id s) ⟩
                id ⋆ id
              ≡⟨ ⋆IdL id ⟩
                id
              ∎

        fg≡id : g ⋆c f ≡ id-c
        fg≡id = Iso-MorPathTransport .Iso.fun MorPathTransport-fg-id

        gf≡id : f ⋆c g ≡ id-c
        gf≡id = Iso-MorPathTransport .Iso.fun MorPathTransport-gf-id

    Iso-ContIso-ΣIsoIso : Iso (CatIso Cont C D) (ΣIsoIso C D)
    Iso-ContIso-ΣIsoIso = iso ContIso→ΣIsoIso ΣIsoIso→ContIso _ _

  open isUnivalent

  module _ (isUnivalentℬ : isUnivalent ℬ) where
    open isUnivalent isUnivalentℬ using () renaming (univ to univℬ)

    Iso-CatIso-Path : ∀ {C D : Container} → Iso (CatIso Cont C D) (C ≡ D)
    Iso-CatIso-Path = iso _ pathToIso _ _

    isUnivalentCont : isUnivalent Cont
    isUnivalentCont .univ C D = TypeIso.isoToIsEquiv (TypeIso.invIso Iso-CatIso-Path)