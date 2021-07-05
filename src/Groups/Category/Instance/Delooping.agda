{-# OPTIONS --without-K --safe #-}

-- The delooping of a Group.
module Groups.Category.Instance.Delooping where

open import Level

open import Data.Unit

open import Categories.Category

open import Groups.Category.Instance.Groups

Deloop : ∀ {c ℓ} → Group c ℓ → Category 0ℓ c ℓ
Deloop G = record
  { Obj = ⊤
  ; _⇒_ = λ _ _ → G.Carrier
  ; _≈_ = G._≈_
  ; id = G.ε
  ; _∘_ = G._∙_
  ; assoc = λ {_ _ _ _ x y z} → G.assoc z y x
  ; sym-assoc = λ {_ _ _ _ x y z} → G.sym (G.assoc z y x)
  ; identityˡ = λ {_ _ x} → G.identityˡ x
  ; identityʳ = λ {_ _ x} → G.identityʳ x
  ; identity² = G.identityˡ G.ε
  ; equiv = G.isEquivalence
  ; ∘-resp-≈ = G.∙-cong
  }
  where
    module G = Group G
