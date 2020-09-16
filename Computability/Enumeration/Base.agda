{-# OPTIONS --without-K #-}
module Computability.Enumeration.Base where

open import Computability.Prelude
open import Computability.Function

record Enumerable (A : Set) : Set where
  field
    enum : ℕ → A
    bijective : Bijective enum

open Enumerable

ℕ-Enumerable : Enumerable ℕ
enum ℕ-Enumerable n = n
proj₁ (bijective ℕ-Enumerable) eq = eq
proj₁ (proj₂ (bijective ℕ-Enumerable) y) = y
proj₂ (proj₂ (bijective ℕ-Enumerable) y) = refl

