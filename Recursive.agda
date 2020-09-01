module Recursive where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Fin using (Fin)

data RecFun : ℕ → Set where
    Var : ∀ {n} → Fin n → RecFun n
    Zero : RecFun 0
    Suc : RecFun 1
    Compose : ∀ {n m} → (Fin n → RecFun m) → RecFun n → RecFun m
    Rec : ∀ {n} → RecFun n → RecFun (2 + n) → RecFun (1 + n)
    Mu : ∀ {n} → RecFun (1 + n) → RecFun n

