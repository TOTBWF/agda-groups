{-# OPTIONS --without-K --safe #-}

-- Normal Subgroups
module Groups.Subgroup.Normal where

open import Level
open import Function using (_$_)

import Relation.Binary.Reasoning.Setoid as SR

open import Categories.Object.Kernel

open import Categories.Morphism
open import Categories.Morphism.Normal

open import Groups.Category.Instance.Groups
open import Groups.Category.Instance.Groups.Properties

open import Groups.Objects.Kernel

open import Groups.Subgroup

open GroupHomomorphism public

private
  variable
    c ℓ : Level


-- Let's define normal subgroups in terms of normal monomorphisms
_◁_ : (G H : Group c ℓ) → Set (suc c ⊔ suc ℓ)
_◁_ {c = c} {ℓ = ℓ} G H = NormalMonomorphism (Groups c ℓ) (𝟎 c ℓ) G H



normal-subgroup : ∀ {G H : Group c ℓ} → G ◁ H → G ⊆ H
normal-subgroup normal = record
  { mor = normal.mor
  ; mono = normal.mono
  }
  where
    module normal = NormalMonomorphism normal

-- Bundled Form
record NormalSubgroup (G : Group c ℓ) : Set (suc c ⊔ suc ℓ) where
  field
    group : Group c ℓ
    is-normal : group ◁ G

  open Group group public

  inj : GroupHomomorphism group G
  inj = NormalMonomorphism.mor is-normal

  subgroup : Subgroup G
  subgroup = record
    { group = group
    ; is-subgroup = normal-subgroup is-normal
    }


-- Normal subgroups are invariant under conjugation
module _ {c ℓ} {G N : Group (c ⊔ ℓ) ℓ} (normal : N ◁ G) where
  private
    open NormalMonomorphism normal renaming (mor to inj; arr to ϕ; B to H)

    module G = Group G
    module N = Group N
    module H = Group H

    open SR H.setoid

    K : Kernel (𝟎 (c ⊔ ℓ) ℓ) ϕ
    K = (IsKernel⇒Kernel (𝟎 (c ⊔ ℓ) ℓ) isKernel)

  normal-conj : ∀ (n : N.Carrier) → (g : G.Carrier) → (g G.∙ ⟦ inj ⟧ n G.∙ (g G.⁻¹)) ∈ normal-subgroup normal 
  normal-conj n g = identity-kernel {c = c} K $ begin
    ⟦ ϕ ⟧ (g G.∙ ⟦ inj ⟧ n G.∙ g G.⁻¹)               ≈⟨ homo ϕ (g G.∙ ⟦ inj ⟧ n) (g G.⁻¹) ⟩
    ⟦ ϕ ⟧ (g G.∙ ⟦ inj ⟧ n) H.∙ ⟦ ϕ ⟧ (g G.⁻¹)       ≈⟨ H.∙-congʳ (homo ϕ g (⟦ inj ⟧ n)) ⟩
    ⟦ ϕ ⟧ g H.∙ ⟦ ϕ ⟧ (⟦ inj ⟧ n) H.∙ ⟦ ϕ ⟧ (g G.⁻¹) ≈⟨ H.∙-congʳ (H.∙-congˡ (kernel-identity {c = c} K (inclusion-∈ (kernel-subgroup {c = c} K) n))) ⟩
    ⟦ ϕ ⟧ g H.∙ H.ε H.∙ ⟦ ϕ ⟧ (g G.⁻¹)               ≈⟨ H.∙-congʳ (H.identityʳ (⟦ ϕ ⟧ g)) ⟩
    ⟦ ϕ ⟧ g H.∙ ⟦ ϕ ⟧ (g G.⁻¹)                       ≈˘⟨ homo ϕ g (g G.⁻¹) ⟩
    ⟦ ϕ ⟧ (g G.∙ g G.⁻¹)                             ≈⟨ cong ϕ (G.inverseʳ g) ⟩
    ⟦ ϕ ⟧ G.ε                                        ≈⟨ ε-homo ϕ ⟩
    H.ε                                              ∎

module _ {c ℓ} {G H : Group (c ⊔ ℓ) ℓ} (subset : G ⊆ H) where
  private
    module G = Group G
    module H = Group H
    open _↣_ subset renaming (mor to inj)

  -- Need quotients for this...
  -- conj-normal : (∀ (g : G.Carrier) → (h : H.Carrier) → (h H.∙ ⟦ inj ⟧ g H.∙ (h H.⁻¹)) ∈ subset) → G ◁ H
  -- conj-normal invariant = record
  --   { mor = inj
  --   ; isNormalMonomorphism = record
  --     { B = {!!} -- This should be H/G
  --     ; arr = {!!}
  --     ; isKernel = {!!}
  --     }
  --   }
