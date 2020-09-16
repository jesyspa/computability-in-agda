{-# OPTIONS --without-K #-}
module Computability.Function where

open import Computability.Prelude
import Function

variable
  l₀ l₁ : Level

Injective : {A : Set l₀}{B : Set l₁} → (A → B) → Set _
Injective = Function.Injective _≡_ _≡_

Surjective : {A : Set l₀}{B : Set l₁} → (A → B) → Set _
Surjective {A = A} {B = B} = Function.Surjective {A = A} {B = B} _≡_ _≡_

Bijective : {A : Set l₀}{B : Set l₁} → (A → B) → Set _
Bijective = Function.Bijective _≡_ _≡_
