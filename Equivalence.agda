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
