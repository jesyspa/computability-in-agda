module Computability.Data.Nat.Iteration where

open import Computability.Prelude

iterate : {A : Set} → (A → A) → ℕ → A → A
iterate f zero a = a
iterate f (suc n) a = f (iterate f n a)

split-iterate : {A : Set}(f : A → A)(a : A)
              → (n m : ℕ)
              → iterate f (n + m) a ≡ iterate f n (iterate f m a)
split-iterate f a zero m = refl
split-iterate f a (suc n) m rewrite split-iterate f a n m = refl

