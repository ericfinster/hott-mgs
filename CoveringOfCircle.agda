--
--  CoveringOfCircle - the universal cover of the circle
--

open import Prelude
open import Equivalence
open import Circle

module CoveringOfCircle where

  -- data ℤ : Type where
  --   pos : ℕ → ℤ 
  --   neg : ℕ → ℤ

  -- shift : ℤ → ℤ
  -- shift (pos x) = {!!}
  -- shift (neg x) = {!!}
  
  data Bool : Type where
    true : Bool
    false : Bool
    
  neg : Bool → Bool
  neg true = false
  neg false = true

  neg-is-equiv : is-equiv neg
  neg-is-equiv = record { inv-l = neg ; inv-r = neg ; η = λ { true → refl ; false → refl } ; ϵ = λ { true → refl ; false → refl } } 

  double-cover : S¹ → Type
  double-cover = S¹-rec Bool (equiv-to-id (neg , neg-is-equiv))

  purported-section : (s : S¹) → double-cover s
  purported-section = {!!} 

  
