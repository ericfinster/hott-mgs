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
    
    -- Exercise 2.2
    transport-equiv : ∀ {P : X → Type ℓ₁}{x y : X}{p : x ≡ y} → is-equiv (transport P p)
    transport-equiv {P}{x}{y}{p} = record { 
      inv-l = transport P (sym p) ; 
      inv-r = transport P (sym p) ; 
      η = lem1 p ; 
      ϵ = lem2 p }

        where
          lem1 : ∀ {x y : X} (p : x ≡ y) (Px : P x) → transport P (sym p) (transport P p Px) ≡ Px
          lem1 refl _ = refl
          lem2 : ∀ {x y : X} (p : x ≡ y) (Py : P y) → transport P p (transport P (sym p) Py) ≡ Py
          lem2 refl _ = refl
    
    -- Exercise 2.3
    transport-comp : ∀ {x y z : X} (p : y ≡ z) → transport (λ w → x ≡ w) p ≡ ((_∙ p))
    transport-comp refl = funext λ q → sym(unit-r q)
    

  id-equiv : ∀ {ℓ} (X : Type ℓ) → X ≃ X
  id-equiv X = (λ x → x) , record { inv-l = λ x → x ; inv-r = λ x → x ; η = λ x → refl ; ϵ = λ x → refl } 

  id-to-equiv : ∀ {ℓ} (X Y : Type ℓ) → X ≡ Y → X ≃ Y
  id-to-equiv X .X refl = id-equiv X

  open is-equiv
  
  postulate

    ua : ∀ {ℓ} {X Y : Type ℓ} → is-equiv (id-to-equiv X Y)

  equiv-to-id : ∀ {ℓ} {X Y : Type ℓ} → X ≃ Y → X ≡ Y
  equiv-to-id {X = X} {Y} e = inv-l (ua {X = X} {Y}) e  

