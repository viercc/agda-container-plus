------------------------------------------------------------------------
-- Pattern synonyms to construct records in Algebra.Structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Algebra.Structures.PatternSynonyms
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Definitions _≈_
import Algebra.Consequences.Setoid as Consequences
open import Data.Product.Base using (_,_)

pattern mkIsMagma isEquivalence ∙-cong =
  record {isEquivalence = isEquivalence; ∙-cong = ∙-cong}

pattern mkIsCommutativeMagma isEquivalence ∙-cong comm =
  record {isMagma = mkIsMagma isEquivalence ∙-cong; comm = comm}

pattern mkIsSemigroup isEquivalence ∙-cong assoc = 
  record {isMagma = mkIsMagma isEquivalence ∙-cong; assoc = assoc}

pattern mkIsCommutativeSemigroup isEquivalence ∙-cong assoc comm =
  record {isSemigroup = mkIsSemigroup isEquivalence ∙-cong assoc; comm = comm}

pattern mkIsMonoid isEquivalence ∙-cong assoc identityˡ identityʳ =
  record {
    isSemigroup = mkIsSemigroup isEquivalence ∙-cong assoc;
    identity = identityˡ , identityʳ
    }

pattern mkIsCommutativeMonoid isEquivalence ∙-cong assoc identityˡ identityʳ comm =
  record {
      isMonoid = mkIsMonoid isEquivalence ∙-cong assoc identityˡ identityʳ;
      comm = comm
    }

pattern mkIsGroup
  isEquivalence ∙-cong assoc identityˡ identityʳ inverseˡ inverseʳ ⁻¹-cong =
  record {
    isMonoid = mkIsMonoid isEquivalence ∙-cong assoc identityˡ identityʳ;
    inverse = inverseˡ , inverseʳ;
    ⁻¹-cong = ⁻¹-cong
    }
