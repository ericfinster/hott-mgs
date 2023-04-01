--
--  Prelude.agda - Foundational definitions 
--

module Prelude where

--
--  Sorts and Levels
--

open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max
           ; Set   to Type
           ; Setω  to Typeω )
open import Agda.Builtin.Sigma public

--
--  Sigma Types
--

open import Agda.Builtin.Sigma public

-- Σ-types
infix 2 Σ-syntax

Σ-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

--
--  Natural Numbers
--

open import Agda.Builtin.Nat public
  using (zero; suc)
  renaming (Nat to ℕ)

--
--  Useful functions
--

infixr 40 _∘_ 

_∘_ : ∀ {ℓ₀ ℓ₁ ℓ₂} {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
  → (f : B → C) (g : A → B) → A → C
(f ∘ g) x = f (g x) 

cst : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → B → A → B
cst b _ = b


data _≡_ {ℓ} {X : Type ℓ} : X → X → Type ℓ where
  refl : {x : X} → x ≡ x 

infixr 30 _≡⟨_⟩_
infixl 40 _∎

_≡⟨_⟩_ : ∀ {ℓ} {X : Type ℓ} (x : X) {y : X} (p : x ≡ y) {z : X} (q : y ≡ z) → x ≡ z
x ≡⟨ refl ⟩ refl = refl

_∎ : ∀ {ℓ} {X : Type ℓ} (x : X) → x ≡ x
x ∎ = refl 

_~_ : ∀ {ℓ} {X Y : Type ℓ} (f g : X → Y) → Type ℓ
_~_ {X = X} f g = (x : X) → f x ≡ g x 

postulate

  funext : ∀ {ℓ} {X Y : Type ℓ} {f g : X → Y} → f ~ g → f ≡ g 

