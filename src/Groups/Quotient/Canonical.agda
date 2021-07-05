{-# OPTIONS --without-K --safe #-}
module Groups.Quotient.Canonical where

open import Level

open import Data.Product

import Algebra.Properties.Group as GP

open import Groups.Category.Instance.Groups
open import Groups.Category.Instance.Delooping

open import Relation.Binary using (Setoid)

open import Groups.Coset
open import Groups.Subgroup
open import Groups.Subgroup.Normal

import Categories.Morphism.Reasoning as MR
import Relation.Binary.Reasoning.Setoid as SR

open GroupHomomorphism public

_/_ : ∀ {c ℓ} (G : Group (c ⊔ ℓ) ℓ) (H : NormalSubgroup G) → Group (c ⊔ ℓ) (c ⊔ ℓ)
_/_ {c = c} {ℓ = ℓ} G H-Normal = record
  { Carrier = LeftCoset.Carrier
  ; _≈_ = LeftCoset._≈_
  ; _∙_ = G._∙_
  ; ε = G.ε
  ; _⁻¹ = G._⁻¹ 
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = LeftCoset.isEquivalence
          ; ∙-cong = λ { {g₁} {g₂} {g₃} {g₄} (h₁ , eq₁) (h₂ , eq₂) →
            let (h₃ , eq₃) = normal-coset-from {c = c} G H-Normal g₃ (⟦ H-Normal.inj ⟧ h₁ G.∙ g₃) (h₁ , G.refl)
            in (h₃ H.∙ h₂) , (begin
              (g₁ G.∙ g₃) G.∙ ⟦ H-Normal.inj ⟧ (h₃ H.∙ h₂)                  ≈⟨ G.∙-congˡ (homo H-Normal.inj h₃ h₂) ⟩
              (g₁ G.∙ g₃) G.∙ (⟦ H-Normal.inj ⟧ h₃ G.∙ ⟦ H-Normal.inj ⟧ h₂) ≈⟨ center eq₃ ⟩
              g₁ G.∙ ((⟦ H-Normal.inj ⟧ h₁ G.∙ g₃) G.∙ ⟦ H-Normal.inj ⟧ h₂) ≈⟨ pull-first eq₁ ⟩
              g₂ G.∙ (g₃ G.∙ ⟦ H-Normal.inj ⟧ h₂)                         ≈⟨ G.∙-congˡ eq₂ ⟩
              g₂ G.∙ g₄ ∎) }
          }
        ; assoc = λ x y z → left-coset-lift {c = c} G H-Normal.subgroup (x G.∙ y G.∙ z) (x G.∙ (y G.∙ z)) (G.assoc x y z)
        }
      ; identity = (λ x → left-coset-lift {c = c} G H-Normal.subgroup (G.ε G.∙ x) x (G.identityˡ x)) , (λ x → left-coset-lift {c = c} G H-Normal.subgroup (x G.∙ G.ε) x (G.identityʳ x))
      }
    ; inverse = (λ x → left-coset-lift {c = c} G H-Normal.subgroup (x G.⁻¹ G.∙ x) G.ε (G.inverseˡ x)) , (λ x → left-coset-lift {c = c} G H-Normal.subgroup (x G.∙ x G.⁻¹ ) G.ε (G.inverseʳ x))
    ; ⁻¹-cong = λ { {g₁} {g₂} (h , eq) →
      let (h′ , eq′) = normal-coset-to {c = c} G H-Normal g₁ g₂ ((h , eq))
      in (h′ H.⁻¹) , (begin
      g₁ G.⁻¹ G.∙ ⟦ H-Normal.inj ⟧ (h′ H.⁻¹) ≈⟨ G.∙-congˡ (⁻¹-homo H-Normal.inj h′) ⟩
      (g₁ G.⁻¹ G.∙ ⟦ H-Normal.inj ⟧ h′ G.⁻¹) ≈˘⟨ ⁻¹-anti-homo-∙ (⟦ H-Normal.inj ⟧ h′) g₁ ⟩
      ((⟦ H-Normal.inj ⟧ h′ G.∙ g₁) G.⁻¹) ≈⟨ G.⁻¹-cong eq′ ⟩
      (g₂ G.⁻¹) ∎) }
    }
  }
  where
    module G = Group G
    module H-Normal = NormalSubgroup H-Normal
    module H = Group H-Normal.group
    module LeftCoset = Setoid (LeftCoset G H-Normal.subgroup)
    module RightCoset = Setoid (RightCoset G H-Normal.subgroup)
    open SR G.setoid
    open MR (Deloop G)
    open GP G
