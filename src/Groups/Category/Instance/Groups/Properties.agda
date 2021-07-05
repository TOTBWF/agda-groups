{-# OPTIONS --without-K --safe #-}

module Groups.Category.Instance.Groups.Properties where

open import Level
open import Data.Unit.Polymorphic
open import Data.Product using (_,_)

open import Categories.Object.Zero

open import Groups.Category.Instance.Groups

open GroupHomomorphism

𝟎 : ∀ c ℓ → Zero (Groups c ℓ)
𝟎 _ _ = record
  { 𝟘 = record
    { Carrier = ⊤
    ; _≈_ = λ _ _ → ⊤
    ; _∙_ = λ _ _ → tt
    ; ε = tt
    ; _⁻¹ = λ _ → tt
    ; isGroup = record
      { isMonoid =
        record
        { isSemigroup =
          record
          { isMagma =
            record
            { isEquivalence =
              record
              { refl = tt
              ; sym = λ _ → tt
              ; trans = λ _ _ → tt
              }
            ; ∙-cong = λ _ _ → tt
            }
          ; assoc = λ _ _ _ → tt
          }
        ; identity = (λ _ → tt) , (λ _ → tt)
        }
      ; inverse = (λ _ → tt) , (λ _ → tt)
      ; ⁻¹-cong = λ _ → tt
      }
    }
  ; isZero = record
    { isInitial = record
      { ! = λ {G} →
        let open Group G
        in record
          { ⟦_⟧ = λ _ → ε
          ; cong = λ _ → refl
          ; homo = λ _ _ → sym (identityʳ ε)
          }
      ; !-unique = λ {G} f tt →
        let open Group G
        in sym (ε-homo f)
      }
    ; isTerminal = record
      { ! = record
        { ⟦_⟧ = λ _ → tt
        ; cong = λ _ → tt
        ; homo = λ _ _ → tt
        }
      ; !-unique = λ _ _ → tt
      }
    }
  }
