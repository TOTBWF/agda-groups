{-# OPTIONS --without-K --safe #-}

module Groups.Objects.Kernel.Canonical where

open import Level
open import Function using (_$_)

open import Data.Product using (proj₂)

open import Algebra.Properties.Group

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Object.Kernel
open import Categories.Object.Kernel.Properties

open import Groups.Category.Instance.Groups
open import Groups.Category.Instance.Groups.Properties

open import Groups.Subgroup

open GroupHomomorphism

private
  variable
    c ℓ : Level

module _ {G H : Group (c ⊔ ℓ) ℓ} (f : GroupHomomorphism G H) where
  private
    module G = Group G
    module H = Group H

  CanonicalKernel : Group (c ⊔ ℓ) ℓ
  CanonicalKernel = mk-subgroup G P ∙-closed ε-closed ⁻¹-closed
    where
      open SR H.setoid
  
      P : G.Carrier → Set _
      P g = ⟦ f ⟧ g H.≈ H.ε
  
      ∙-closed : ∀ x y → P x → P y → P (x G.∙ y)
      ∙-closed x y px py = begin
        ⟦ f ⟧ (x G.∙ y)     ≈⟨ homo f x y ⟩
        ⟦ f ⟧ x H.∙ ⟦ f ⟧ y ≈⟨ H.∙-cong px py ⟩
        H.ε H.∙ H.ε         ≈⟨ H.identityʳ H.ε ⟩
        H.ε ∎
  
      ε-closed : P G.ε
      ε-closed = ε-homo f
  
      ⁻¹-closed : ∀ x → P x → P (x G.⁻¹)
      ⁻¹-closed x px = begin
        ⟦ f ⟧ (x G.⁻¹) ≈⟨ ⁻¹-homo f x ⟩
        (⟦ f ⟧ x H.⁻¹) ≈⟨ H.⁻¹-cong px ⟩
        H.ε H.⁻¹       ≈⟨ ε⁻¹≈ε H ⟩
        H.ε            ∎

  -- FIXME: Put this in a different place
  CanonicalKernel⇒Kernel : ∀ (K : Kernel (𝟎 (c ⊔ ℓ) ℓ) f) → GroupHomomorphism CanonicalKernel (Kernel.kernel K)
  CanonicalKernel⇒Kernel K = Kernel.universal K {h = subgroup-inj G} proj₂
