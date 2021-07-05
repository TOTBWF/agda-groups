{-# OPTIONS --without-K --safe #-}

-- Quotient Groups, defined categorically
module Groups.Quotient where

open import Level

open import Categories.Category
open import Categories.Object.Kernel

open import Groups.Category.Instance.Groups
open import Groups.Category.Instance.Groups.Properties
open import Groups.Subgroup.Normal


-- FIXME: This could probably be factored out into agda-categories
record IsQuotient {c ℓ} (G : Group c ℓ) (H : NormalSubgroup G) (Q : Group c ℓ) : Set (suc c ⊔ suc ℓ) where
  private
    module H = NormalSubgroup H
    open Category (Groups c ℓ)
  field
    arr : GroupHomomorphism G Q
    -- The kernel of 'arr' is 'H'
    is-kernel : IsKernel (𝟎 c ℓ) H.inj arr
    -- If there is some other map into a group G′ that has H as the kernel, then there exists a universal map from Q into G′
    universal : ∀ {G′ : Group c ℓ} → (ϕ : G ⇒ G′) → IsKernel (𝟎 c ℓ) H.inj ϕ → Q ⇒ G′
    commute   : ∀ {G′ : Group c ℓ} → (ϕ : G ⇒ G′) → (k : IsKernel (𝟎 c ℓ) H.inj ϕ) → universal ϕ k ∘ arr ≈ ϕ
    unique    : ∀ {G′ : Group c ℓ} → (ϕ : G ⇒ G′) → (k : IsKernel (𝟎 c ℓ) H.inj ϕ) → (ψ : Q ⇒ G′) → ψ ∘ arr ≈ ϕ → ψ ≈ universal ϕ k

record Quotient {c ℓ} (G : Group c ℓ) (H : NormalSubgroup G) : Set (suc c ⊔ suc ℓ) where
  field
    Q : Group c ℓ
    is-quotient : IsQuotient G H Q

  open IsQuotient is-quotient public
