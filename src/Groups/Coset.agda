{-# OPTIONS --without-K --safe #-}
module Groups.Coset where

open import Level

open import Data.Product

import Algebra.Properties.Group as GP

open import Groups.Category.Instance.Groups
open import Groups.Category.Instance.Delooping

open import Relation.Binary using (Setoid)

open import Groups.Subgroup
open import Groups.Subgroup.Normal

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as SR

open GroupHomomorphism public

-- Instead of thinking about cosets as sets directly, we work with
-- elements of 'g', and think about the action of multiplication by 'g'
-- on every element of the subgroup.
LeftCoset : ∀ {c ℓ} (G : Group c ℓ) (H : Subgroup G) → Setoid c (c ⊔ ℓ)
LeftCoset G H-Subgroup = record
  { Carrier = G.Carrier
  ; _≈_ =  λ g₁ g₂ → Σ[ h ∈ H.Carrier ] g₁ G.∙ ⟦ H-Subgroup.inj ⟧ h G.≈ g₂
  ; isEquivalence = record
    { refl = λ {g} → H.ε , (begin
      g G.∙ ⟦ H-Subgroup.inj ⟧ H.ε ≈⟨ G.∙-congˡ (ε-homo H-Subgroup.inj) ⟩
      g G.∙ G.ε                    ≈⟨ G.identityʳ g ⟩
      g                            ∎)
    ; sym = λ { {g₁} {g₂} (h , eq) → (h H.⁻¹) , (begin
      g₂ G.∙ ⟦  H-Subgroup.inj ⟧ (h H.⁻¹)                       ≈⟨ G.∙-cong (G.sym eq) (⁻¹-homo H-Subgroup.inj h) ⟩
      g₁ G.∙ ⟦ H-Subgroup.inj ⟧ h G.∙ ⟦ H-Subgroup.inj ⟧ h G.⁻¹ ≈⟨ cancelʳ (G.inverseʳ (⟦ H-Subgroup.inj ⟧ h)) ⟩
      g₁                                                        ∎) }
    ; trans = λ { {g₁} {g₂} {g₃} (h₁ , eq₁) (h₂ , eq₂)  → (h₁ H.∙ h₂) , (begin
      g₁ G.∙ ⟦ H-Subgroup.inj ⟧ (h₁ H.∙ h₂)                  ≈⟨ pushʳ (homo H-Subgroup.inj h₁ h₂) ⟩
      g₁ G.∙ ⟦ H-Subgroup.inj ⟧ h₁ G.∙ ⟦ H-Subgroup.inj ⟧ h₂ ≈⟨ G.∙-congʳ eq₁ ⟩
      g₂ G.∙ ⟦ H-Subgroup.inj ⟧ h₂                           ≈⟨ eq₂ ⟩
      g₃                                                     ∎) }
    }
  }
  where
    module G = Group G
    module H-Subgroup = Subgroup H-Subgroup
    module H = Group H-Subgroup.group
    open SR G.setoid
    open MR (Deloop G)

RightCoset : ∀ {c ℓ} (G : Group c ℓ) (H : Subgroup G) → Setoid c (c ⊔ ℓ)
RightCoset G H-Subgroup = record
  { Carrier = G.Carrier
  ; _≈_ =  λ g₁ g₂ → Σ[ h ∈ H.Carrier ] ⟦ H-Subgroup.inj ⟧ h G.∙ g₁ G.≈ g₂
  ; isEquivalence = record
    { refl = λ {g} → H.ε , (begin
      ⟦ H-Subgroup.inj ⟧ H.ε G.∙ g ≈⟨ G.∙-congʳ (ε-homo H-Subgroup.inj) ⟩
      G.ε G.∙ g                    ≈⟨ G.identityˡ g ⟩
      g                            ∎)
    ; sym = λ { {g₁} {g₂} (h , eq) → (h H.⁻¹) , (begin
      ⟦ H-Subgroup.inj ⟧ (h H.⁻¹) G.∙ g₂                          ≈⟨ G.∙-cong (⁻¹-homo H-Subgroup.inj h) (G.sym eq) ⟩
      ⟦ H-Subgroup.inj ⟧ h G.⁻¹ G.∙ (⟦ H-Subgroup.inj ⟧ h G.∙ g₁) ≈⟨ cancelˡ (G.inverseˡ (⟦ H-Subgroup.inj ⟧ h)) ⟩
      g₁                                                          ∎) }
    ; trans = λ { {g₁} {g₂} {g₃} (h₁ , eq₁) (h₂ , eq₂) → (h₂ H.∙ h₁) , (begin
      (⟦ H-Subgroup.inj ⟧ (h₂ H.∙ h₁) G.∙ g₁)                    ≈⟨ pushˡ (homo H-Subgroup.inj h₂ h₁) ⟩
      (⟦ H-Subgroup.inj ⟧ h₂ G.∙ (⟦ H-Subgroup.inj ⟧ h₁ G.∙ g₁)) ≈⟨ G.∙-congˡ eq₁ ⟩
      (⟦ H-Subgroup.inj ⟧ h₂ G.∙ g₂)                             ≈⟨ eq₂ ⟩
      g₃                                                         ∎) }
    }
  }
  where
    module G = Group G
    module H-Subgroup = Subgroup H-Subgroup
    module H = Group H-Subgroup.group
    open SR G.setoid
    open MR (Deloop G)

module _ {c ℓ} (G : Group (c ⊔ ℓ) ℓ) (H-Subgroup : Subgroup G) where
  private
    module G = Group G
    module H-Subgroup = Subgroup H-Subgroup
    module H = Group (H-Subgroup.group)
    module LeftCoset = Setoid (LeftCoset G H-Subgroup)
    module RightCoset = Setoid (RightCoset G H-Subgroup)

  -- We can lift equalities in 'G' to equalities on coset elements
  left-coset-lift : ∀ g₁ g₂ → g₁ G.≈ g₂ → g₁ LeftCoset.≈ g₂
  left-coset-lift g₁ g₂ eq = H.ε , (begin
    g₁ G.∙ ⟦ H-Subgroup.inj ⟧ H.ε ≈⟨ elimʳ (ε-homo H-Subgroup.inj) ⟩
    g₁ ≈⟨ eq ⟩
    g₂ ∎)
    where
      open SR G.setoid
      open MR (Deloop G)

  right-coset-lift : ∀ g₁ g₂ → g₁ G.≈ g₂ → g₁ RightCoset.≈ g₂
  right-coset-lift g₁ g₂ eq = H.ε , (begin
    ⟦ H-Subgroup.inj ⟧ H.ε G.∙ g₁ ≈⟨ elimˡ (ε-homo H-Subgroup.inj) ⟩
    g₁ ≈⟨ eq ⟩
    g₂ ∎)
    where
      open SR G.setoid
      open MR (Deloop G)

module _ {c ℓ} (G : Group (c ⊔ ℓ) ℓ) (H-Normal : NormalSubgroup G) where
  private
    module G = Group G
    module H-Normal = NormalSubgroup H-Normal
    module LeftCoset = Setoid (LeftCoset G H-Normal.subgroup)
    module RightCoset = Setoid (RightCoset G H-Normal.subgroup)

  abstract

    -- Left Cosets are the same as Right cosets
    normal-coset-to : ∀ g₁ g₂ → g₁ LeftCoset.≈ g₂ → g₁ RightCoset.≈ g₂
    normal-coset-to g₁ g₂ (h , eq) =
      let module conj-invariant = _∈_ (normal-conj {c = c} H-Normal.is-normal h g₁)
      in conj-invariant.fiber , (begin
        ⟦ H-Normal.inj ⟧ conj-invariant.fiber G.∙ g₁ ≈⟨ G.∙-congʳ conj-invariant.in-fiber ⟩
        g₁ G.∙ ⟦ H-Normal.inj ⟧ h G.∙ g₁ G.⁻¹ G.∙ g₁ ≈⟨ cancelʳ (G.inverseˡ g₁) ⟩
        g₁ G.∙ ⟦ H-Normal.inj ⟧ h                    ≈⟨ eq ⟩
        g₂                                           ∎)
      where
        open SR G.setoid
        open MR (Deloop G)
  
    normal-coset-from : ∀ g₁ g₂ → g₁ RightCoset.≈ g₂ → g₁ LeftCoset.≈ g₂
    normal-coset-from g₁ g₂ (h , eq) =
      let module conj-invariant = _∈_ (normal-conj {c = c} H-Normal.is-normal h (g₁ G.⁻¹))
      in conj-invariant.fiber , (begin
        g₁ G.∙ ⟦ H-Normal.inj ⟧ conj-invariant.fiber                 ≈⟨ G.∙-congˡ conj-invariant.in-fiber ⟩
        g₁ G.∙ (g₁ G.⁻¹ G.∙ ⟦ H-Normal.inj ⟧ h G.∙ ((g₁ G.⁻¹) G.⁻¹)) ≈⟨ pull-first (G.inverseʳ g₁) ⟩
        G.ε G.∙ (⟦ H-Normal.inj ⟧ h G.∙ (g₁ G.⁻¹) G.⁻¹)              ≈⟨ G.identityˡ (⟦ H-Normal.inj ⟧ h G.∙ (g₁ G.⁻¹) G.⁻¹) ⟩
        ⟦ H-Normal.inj ⟧ h G.∙ (g₁ G.⁻¹) G.⁻¹                        ≈⟨ G.∙-congˡ (⁻¹-involutive g₁) ⟩
        ⟦ H-Normal.inj ⟧ h G.∙ g₁                                    ≈⟨ eq ⟩
        g₂ ∎)
      where
        open SR G.setoid
        open MR (Deloop G)
        open GP G
