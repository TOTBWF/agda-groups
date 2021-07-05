{-# OPTIONS --without-K --safe #-}

-- Kernels of homomorphisms

open import Level
open import Groups.Category.Instance.Groups

-- Properties of kernels of group homomorphisms
module Groups.Objects.Kernel where

open import Data.Product using (_,_)

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Object.Kernel
open import Categories.Object.Kernel.Properties

open import Groups.Category.Instance.Groups.Properties

open import Groups.Objects.Kernel.Canonical

open import Groups.Subgroup

module _ {c ℓ} {G H : Group (c ⊔ ℓ) ℓ} {f : GroupHomomorphism G H} (K : Kernel (𝟎 (c ⊔ ℓ) ℓ) f) where
  private
    module G = Group G
    module H = Group H
    open Kernel K

  kernel-subgroup : kernel ⊆ G
  kernel-subgroup = record
    { mor = kernel⇒
    ; mono = Kernel-Mono (𝟎 (c ⊔ ℓ) ℓ) K
    }

  kernel-identity : ∀ {g : G.Carrier} → g ∈ kernel-subgroup → ⟦ f ⟧ g H.≈ H.ε
  kernel-identity {g} in-kernel = begin
    ⟦ f ⟧ g                   ≈˘⟨ cong f in-fiber ⟩
    ⟦ f ⟧ (⟦ kernel⇒ ⟧ fiber) ≈⟨ commute fiber ⟩
    H.ε ∎
    where
      open SR H.setoid
      open _∈_ in-kernel

  identity-kernel : ∀ {g : G.Carrier} → ⟦ f ⟧ g H.≈ H.ε → g ∈ kernel-subgroup
  identity-kernel {g} to-id = record
    { fiber = ⟦ CanonicalKernel⇒Kernel {c = c ⊔ ℓ} f K ⟧ (g , to-id)
    ; in-fiber = G.sym (factors (g , to-id))
    }
