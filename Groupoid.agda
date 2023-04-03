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

    sym-comp : ∀ {x y : X} (p : x ≡ y) → sym p ∙ p ≡ refl
    sym-comp refl = refl
    
  module _ {ℓ₀ ℓ₁} {X : Type ℓ₀} {Y : Type ℓ₁} where

    ap : (f : X → Y) {x y : X} (p : x ≡ y) → f x ≡ f y
    ap f refl = refl

    ap-comp : (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z) → ap f (p ∙ q) ≡ (ap f p) ∙ (ap f q)
    ap-comp f refl refl = refl

    ap-sym : (f : X → Y) {x y : X} (p : x ≡ y) → sym (ap f p) ≡ ap f (sym p)
    ap-sym f refl = refl
