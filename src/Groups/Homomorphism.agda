{-# OPTIONS --without-K --safe #-}

-- A collection of helpers and facts about group homomorphisms
module Groups.Homomorphism where

open import Level

import Relation.Binary.Reasoning.Setoid as SR

open import Algebra.Bundles
open import Algebra.Morphism.Structures as Mor
import Algebra.Morphism.Definitions as Define

private
  variable
    c ℓ c′ ℓ′ : Level

-- The stdlib provides unbundled versions of group homomorphisms on lawless 'RawGroup's, which
-- are a bit hard to work with. Therefore, we define our own bundled version that operates on a 'Group'.
-- These have the benefit of only having to show that the function is homomorphic on _∙_, which saves a lot
-- of work elsewhere.
record GroupHomomorphism {c c′ ℓ ℓ′} (G : Group c ℓ) (H : Group c′ ℓ′) : Set (c ⊔ c′ ⊔ ℓ ⊔ ℓ′) where
  private
    module G = Group G
    module H = Group H
    open Define G.Carrier H.Carrier H._≈_
    open G using () renaming (_∙_ to _∙ᴳ_; ε to εᴳ; _⁻¹ to _⁻¹ᴳ; _≈_ to _≈ᴳ_)
    open H using () renaming (_∙_ to _∙ᴴ_; ε to εᴴ; _⁻¹ to _⁻¹ᴴ; _≈_ to _≈ᴴ_)
    open SR H.setoid

  field
    ⟦_⟧ : G.Carrier → H.Carrier
    cong : ∀ {x y} → x ≈ᴳ y → ⟦ x ⟧ ≈ᴴ ⟦ y ⟧
    homo : Homomorphic₂ ⟦_⟧ _∙ᴳ_ _∙ᴴ_

  ε-homo : ⟦ εᴳ ⟧ ≈ᴴ εᴴ
  ε-homo = begin
    ⟦ εᴳ ⟧                           ≈˘⟨ H.identityˡ ⟦ εᴳ ⟧ ⟩
    εᴴ ∙ᴴ ⟦ εᴳ ⟧                     ≈˘⟨ H.∙-congʳ (H.inverseˡ ⟦ εᴳ ⟧) ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ⟧ ∙ᴴ ⟦ εᴳ ⟧   ≈⟨ H.assoc (⟦ εᴳ ⟧ ⁻¹ᴴ) ⟦ εᴳ ⟧ ⟦ εᴳ ⟧ ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ (⟦ εᴳ ⟧ ∙ᴴ ⟦ εᴳ ⟧) ≈˘⟨ H.∙-congˡ (homo εᴳ εᴳ) ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ∙ᴳ εᴳ ⟧       ≈⟨ H.∙-congˡ (cong (G.identityʳ εᴳ)) ⟩
    ⟦ εᴳ ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ⟧             ≈⟨ H.inverseˡ ⟦ εᴳ ⟧ ⟩
    εᴴ                               ∎

  ⁻¹-homo : ∀ x → ⟦ x ⁻¹ᴳ ⟧ ≈ᴴ ⟦ x ⟧ ⁻¹ᴴ
  ⁻¹-homo x = begin
    ⟦ x ⁻¹ᴳ ⟧                         ≈˘⟨  H.identityˡ ⟦ x ⁻¹ᴳ ⟧  ⟩
    εᴴ ∙ᴴ ⟦ x ⁻¹ᴳ ⟧                   ≈˘⟨ H.∙-congʳ (H.inverseˡ ⟦ x ⟧) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ ⟦ x ⟧ ∙ᴴ ⟦ x ⁻¹ᴳ ⟧   ≈⟨ H.assoc (⟦ x ⟧ ⁻¹ᴴ) ⟦ x ⟧ ⟦ x ⁻¹ᴳ ⟧ ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ (⟦ x ⟧ ∙ᴴ ⟦ x ⁻¹ᴳ ⟧) ≈˘⟨ H.∙-congˡ (homo x (x ⁻¹ᴳ)) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ ⟦ x ∙ᴳ x ⁻¹ᴳ ⟧       ≈⟨ H.∙-congˡ (cong (G.inverseʳ x)) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ ⟦ εᴳ ⟧               ≈⟨ H.∙-congˡ ε-homo ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∙ᴴ εᴴ                   ≈⟨ H.identityʳ (⟦ x ⟧ ⁻¹ᴴ) ⟩
    ⟦ x ⟧ ⁻¹ᴴ ∎

-- Abbrevation for bundled homomorphisms between abelian groups
AbelianGroupHomomorphism : AbelianGroup c ℓ → AbelianGroup c′ ℓ′ → Set (c ⊔ c′ ⊔ ℓ ⊔ ℓ′)
AbelianGroupHomomorphism G H = GroupHomomorphism (AbelianGroup.group G) (AbelianGroup.group H)
