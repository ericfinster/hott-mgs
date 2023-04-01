--
--  Groupoid.agda - Gropuoid laws
--

open import Prelude

module Groupoid where 

  module _ {ℓ} {X : Type ℓ} where

    infixl 50 _∙_
 
    _∙_ : ∀ {x y z : X} → x ≡ y → y ≡ z → x ≡ z
    refl ∙ refl = refl

    unit-l : ∀ {x y : X} (p : x ≡ y) → refl ∙ p ≡ p
    unit-l refl = refl 

    unit-r : ∀ {x y : X} (p : x ≡ y) → p ∙ refl ≡ p
    unit-r refl = refl

    assoc : ∀ {x y z w : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
    assoc refl refl refl = refl

    sym : ∀ {x y : X} → x ≡ y → y ≡ x
    sym refl = refl
    
  module _ {ℓ₀ ℓ₁} {X : Type ℓ₀} {Y : Type ℓ₁} where

    ap : (f : X → Y) {x y : X} (p : x ≡ y) → f x ≡ f y
    ap f refl = refl 
