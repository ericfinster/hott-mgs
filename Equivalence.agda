--
--  Groupoid.agda - Gropuoid laws
--

open import Prelude
open import Groupoid

module Equivalence where

  record is-equiv {ℓ₀ ℓ₁} {X : Type ℓ₀} {Y : Type ℓ₁} (f : X → Y) : Type (ℓ-max ℓ₀ ℓ₁) where
    field
      inv-l : Y → X
      inv-r : Y → X
      η : (x : X) → inv-l (f x) ≡ x
      ϵ : (y : Y) → f (inv-r y) ≡ y 

  _≃_ : ∀ {ℓ₀ ℓ₁} → Type ℓ₀ → Type ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
  X ≃ Y = Σ[ f ∈ (X → Y) ] is-equiv f
  
  module _ {ℓ₀ ℓ₁} {X : Type ℓ₀} {Y : Type ℓ₁} (f : X → Y) (f-eqv : is-equiv f) where

    open is-equiv f-eqv
    
    inv-l≡inv-r : inv-l ≡ inv-r
    inv-l≡inv-r = funext lem

      where lem : inv-l ~ inv-r
            lem y = inv-l y               ≡⟨ ap inv-l (sym (ϵ y)) ⟩
                    inv-l (f (inv-r y))   ≡⟨ η (inv-r y) ⟩
                    inv-r y ∎ 

  id-equiv : ∀ {ℓ} (X : Type ℓ) → X ≃ X
  id-equiv X = (λ x → x) , record { inv-l = λ x → x ; inv-r = λ x → x ; η = λ x → refl ; ϵ = λ x → refl } 

  id-to-equiv : ∀ {ℓ} (X Y : Type ℓ) → X ≡ Y → X ≃ Y
  id-to-equiv X .X refl = id-equiv X

  open is-equiv
  
  postulate

    ua : ∀ {ℓ} {X Y : Type ℓ} → is-equiv (id-to-equiv X Y)

  equiv-to-id : ∀ {ℓ} {X Y : Type ℓ} → X ≃ Y → X ≡ Y
  equiv-to-id {X = X} {Y} e = inv-l (ua {X = X} {Y}) e  
