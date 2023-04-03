--
--  NType.agda - Truncated types
--

open import Prelude
open import Groupoid

module NType where

  data ℕ₋₂ : Type where
    ⟨-2⟩ : ℕ₋₂
    S : ℕ₋₂ → ℕ₋₂
  
  is-contr : ∀ {ℓ} → Type ℓ → Type ℓ
  is-contr X = Σ[ x ∈ X ] ((y : X) → x ≡ y) 

  is-of-type : ∀ {ℓ} → ℕ₋₂ → Type ℓ → Type ℓ
  is-of-type ⟨-2⟩ X = is-contr X
  is-of-type (S n) X = (x y : X) → is-of-type n (x ≡ y)

  module _ {ℓ₀} {X : Type ℓ₀} where

    is-contr-upwards : {x y : X} → is-contr X → is-contr (x ≡ y)
    is-contr-upwards {x} {y} (c , Q) = sym (Q x) ∙ Q y , rest
      where
        rest : (p : x ≡ y) → sym (Q x) ∙ Q y ≡ p
        rest refl = sym-comp (Q x)
