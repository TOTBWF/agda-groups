{-# OPTIONS --without-K --safe #-}

-- The category of groups
module Groups.Category.Instance.Groups where

open import Level

import Relation.Binary.Reasoning.Setoid as SR

open import Algebra.Bundles using (Group) public

open import Categories.Category

open import Groups.Homomorphism using (GroupHomomorphism) public

open GroupHomomorphism

Groups : ∀ (c ℓ : Level) → Category (suc c ⊔ suc ℓ) (c ⊔ ℓ) (c ⊔ ℓ)
Groups c ℓ = record
  { Obj = Group c ℓ
  ; _⇒_ = GroupHomomorphism
  ; _≈_ = λ {G} {H} f g →
    let module H = Group H
    in ∀ x → (⟦ f ⟧ x) H.≈ (⟦ g ⟧ x)
  ; id = λ {G} →
    let module G = Group G
    in record
      { ⟦_⟧ = λ x → x
      ; cong = λ eq → eq
      ; homo = λ x y → G.refl
      }
  ; _∘_ = λ {G} {H} {I} f g →
    let module G = Group G
        module H = Group H
        module I = Group I
        open SR I.setoid
    in record
      { ⟦_⟧ = λ x → ⟦ f ⟧ (⟦ g ⟧ x)
      ; cong = λ eq → cong f (cong g eq)
      ; homo = λ x y → begin
        ⟦ f ⟧ (⟦ g ⟧ (x G.∙ y))             ≈⟨ cong f (homo g x y) ⟩
        ⟦ f ⟧ (⟦ g ⟧ x H.∙ ⟦ g ⟧ y)         ≈⟨ homo f (⟦ g ⟧ x) (⟦ g ⟧ y) ⟩
        ⟦ f ⟧ (⟦ g ⟧ x) I.∙ ⟦ f ⟧ (⟦ g ⟧ y) ∎
      }
  ; assoc = λ { {D = D} _ → Group.refl D }
  ; sym-assoc = λ { {_} {_} {_} {D} _ → Group.refl D }
  ; identityˡ = λ { {_} {B} _ → Group.refl B }
  ; identityʳ = λ { {_} {B} _ → Group.refl B }
  ; identity² = λ { {A} _ → Group.refl A }
  ; equiv = λ {A} {B} → record
    { refl = λ x → Group.refl B
    ; sym = λ eq x → Group.sym B (eq x)
    ; trans = λ eq₁ eq₂ x → Group.trans B (eq₁ x) (eq₂ x)
    }
  ; ∘-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} eq₁ eq₂ x →
    let module C = Group C
        open SR (C.setoid)
    in begin
      ⟦ f ⟧ (⟦ h ⟧ x) ≈⟨ cong f (eq₂ x) ⟩
      ⟦ f ⟧ (⟦ i ⟧ x) ≈⟨ eq₁ (⟦ i ⟧ x) ⟩
      ⟦ g ⟧ (⟦ i ⟧ x) ∎
  }
