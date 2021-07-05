{-# OPTIONS --without-K --safe #-}

-- Subgroups
module Groups.Subgroup where

open import Level

open import Data.Product using (Σ; _,_; proj₁)

open import Categories.Morphism.Notation
open import Categories.Morphism

open import Groups.Category.Instance.Groups

open GroupHomomorphism public

private
  variable
    c ℓ : Level

-- Subgroups are represented by monomorphisms
_⊆_ : (G H : Group c ℓ) → Set (suc c ⊔ suc ℓ)
_⊆_ {c = c} {ℓ = ℓ} G H = Groups c ℓ [ G ↣ H ]

record Subgroup (G : Group c ℓ) : Set (suc c ⊔ suc ℓ) where
  field
    group : Group c ℓ
    is-subgroup : group ⊆ G

  private
    module is-subgroup = _↣_ is-subgroup

  inj : GroupHomomorphism group G
  inj = is-subgroup.mor

-- Elements of subgroups
record _∈_ {G H : Group c ℓ} (g : Group.Carrier G) (subset : H ⊆ G) : Set (c ⊔ ℓ) where
  private
    module G = Group G
    module H = Group H
    module subset = _↣_ subset 
  field
    fiber : H.Carrier
    in-fiber : ⟦ subset.mor ⟧ fiber G.≈ g

module _ {G H : Group c ℓ} (subset : G ⊆ H) where
  private
    module G = Group G
    module H = Group H
    
 
  inclusion : G.Carrier → H.Carrier
  inclusion = ⟦ _↣_.mor subset ⟧ 
  
  inclusion-∈ : (g : G.Carrier) → inclusion g ∈ subset
  inclusion-∈ g = record
    { fiber = g
    ; in-fiber = H.refl
    }

module _ (G : Group c ℓ) where
  open Group G

  -- Helper for constructing subgroups from predicates
  mk-subgroup : ∀ {p}
             → (P : Carrier → Set p)
             → (∀ x y → P x → P y → P (x ∙ y))
             → P ε
             → (∀ x → P x → P (x ⁻¹))
             → Group (c ⊔ p) ℓ 
  mk-subgroup P ∙-closed ε-closed ⁻¹-closed = record
    { Carrier = Σ Carrier P
    ; _≈_ = λ { (x , _) (y , _) → x ≈ y }
    ; _∙_ = λ { (x , px) (y , py) → (x ∙ y) , (∙-closed x y px py) }
    ; ε = ε , ε-closed
    ; _⁻¹ = λ { (x , px) → x ⁻¹ , ⁻¹-closed x px }
    ; isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = record
              { refl = refl
              ; sym = sym
              ; trans = trans
              }
            ; ∙-cong = ∙-cong
            }
          ; assoc = λ { (x , _) (y , _) (z , _) → assoc x y z }
          }
        ; identity = (λ { (x , _) → identityˡ x }) , (λ { (x , _) → identityʳ x })
        }
      ; inverse = (λ { (x , _) → inverseˡ x }) , (λ { (x , _) → inverseʳ x })
      ; ⁻¹-cong = ⁻¹-cong
      }
    }

  subgroup-inj : ∀ {p}
               → {P : Carrier → Set p}
               → {∙-closed : ∀ x y → P x → P y → P (x ∙ y)}
               → {ε-closed : P ε}
               → {⁻¹-closed : ∀ x → P x → P (x ⁻¹)}
               → GroupHomomorphism (mk-subgroup P ∙-closed ε-closed ⁻¹-closed) G
  subgroup-inj = record
    { ⟦_⟧ = proj₁
    ; cong = λ eq → eq
    ; homo = λ x y → refl
    }
