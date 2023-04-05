--
--  Circle.agda
--

open import Prelude
open import Groupoid

module Circle where

  postulate

    -- Formation
    S¹ : Type

    -- Introduction
    base : S¹
    loop : base ≡ base

    -- Recursor
    S¹-rec : ∀ {ℓ} {C : Type ℓ}
      → (base* : C)
      → (loop* : base* ≡ base*)
      → S¹ → C 

    -- Computation
    S¹-rec-base-β : ∀ {ℓ} {C : Type ℓ}
      → (base* : C)
      → (loop* : base* ≡ base*)
      → S¹-rec base* loop* base ↦ base*
    {-# REWRITE S¹-rec-base-β #-}

    S¹-rec-loop-β : {C : Type}
      → (base* : C)
      → (loop* : base* ≡ base*)
      → ap (S¹-rec base* loop*) loop ↦ loop* 
    {-# REWRITE S¹-rec-loop-β #-}

    -- Elimination
    S¹-elim : {P : S¹ → Type}
      → (base* : P base)
      → (loop* : PathOver P loop base* base*)
      → (s : S¹) → P s 
      
    S¹-elim-base-β : {P : S¹ → Type}
      → (base* : P base)
      → (loop* : PathOver P loop base* base*)
      → S¹-elim base* loop* base ↦ base*
    {-# REWRITE S¹-elim-base-β #-}

    S¹-elim-loop-β : {P : S¹ → Type}
      → (base* : P base)
      → (loop* : PathOver P loop base* base*)
      → apd P (S¹-elim base* loop*) loop ↦ loop*
    {-# REWRITE S¹-elim-loop-β #-}

  
