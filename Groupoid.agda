--
--  Groupoid.agda - Groupoid laws
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

    -- Exercise 2.1
    transport : ∀ {ℓ₁} (P : X → Type ℓ₁) {x y : X} → x ≡ y → P x → P y
    transport P refl w = w
    
  module _ {ℓ₀ ℓ₁} {X : Type ℓ₀} {Y : Type ℓ₁} where

    ap : (f : X → Y) {x y : X} (p : x ≡ y) → f x ≡ f y
    ap f refl = refl

    ap-comp : (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z) → ap f (p ∙ q) ≡ (ap f p) ∙ (ap f q)
    ap-comp f refl refl = refl

    ap-sym : (f : X → Y) {x y : X} (p : x ≡ y) → sym (ap f p) ≡ ap f (sym p)
    ap-sym f refl = refl

  --
  --  Transports and PathOvers
  --

  PathOver : ∀ {ℓ₀ ℓ₁} {X : Type ℓ₀} (P : X → Type ℓ₁)
    → {x y : X} (p : x ≡ y) (a : P x) (b : P y)
    → Type ℓ₁
  PathOver P refl a b = a ≡ b

  apd : ∀ {ℓ₀ ℓ₁} {X : Type ℓ₀} (P : X → Type ℓ₁)
    → (f : (x : X) → P x)
    → {x y : X} (p : x ≡ y)
    → PathOver P p (f x) (f y)
  apd P f refl = refl
