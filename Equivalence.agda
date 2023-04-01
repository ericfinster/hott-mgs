--
--  Groupoid.agda - Gropuoid laws
--

open import Prelude
open import Groupoid

module Equivalence where

  record is-equiv {ℓ} {X Y : Type ℓ} (f : X → Y) : Type ℓ where
    field
      inv-l : Y → X
      inv-r : Y → X
      η : (x : X) → inv-l (f x) ≡ x
      ϵ : (y : Y) → f (inv-r y) ≡ y 

  module _ {ℓ} {X Y : Type ℓ} (f : X → Y) (f-eqv : is-equiv f) where

    open is-equiv f-eqv
    
    inv-l≡inv-r : inv-l ≡ inv-r
    inv-l≡inv-r = funext lem

      where lem : inv-l ~ inv-r
            lem y = inv-l y               ≡⟨ ap inv-l (sym (ϵ y)) ⟩
                    inv-l (f (inv-r y))   ≡⟨ η (inv-r y) ⟩
                    inv-r y ∎ 
