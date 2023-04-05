--
--  Circle.agda
--

open import Prelude

module Circle where

  postulate

    S¹ : Type

    base : S¹
    loop : base ≡ base

    S¹-rec : {C : Type}
      → (base* : C)
      → (loop* : base* ≡ base*)
      → S¹ → C 

    S¹-rec-base-β : {C : Type}
      → (base* : C)
      → (loop* : base* ≡ base*)
      → S¹-rec base* loop* base ↦ base*
    {-# REWRITE S¹-rec-base-β #-}
