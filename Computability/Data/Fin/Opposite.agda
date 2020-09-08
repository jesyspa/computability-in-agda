module Computability.Data.Fin.Opposite where

open import Computability.Prelude
open import Data.Nat using (_≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-step)
open import Data.Fin using (Fin; zero; suc; inject₁; fromℕ; fromℕ<; toℕ; opposite)

opposite-fromℕ : ∀ k → opposite (fromℕ k) ≡ zero
opposite-fromℕ zero = refl
opposite-fromℕ (suc k) rewrite opposite-fromℕ k = refl

opposite-inject₁-suc : ∀{k}(i : Fin k) → opposite (inject₁ i) ≡ suc (opposite i)
opposite-inject₁-suc zero = refl
opposite-inject₁-suc (suc i) rewrite opposite-inject₁-suc i = refl

opposite-opposite : ∀{k}(i : Fin k) → opposite (opposite i) ≡ i
opposite-opposite {suc k} zero rewrite opposite-fromℕ k = refl
opposite-opposite (suc i)
  rewrite opposite-inject₁-suc (opposite i)
        | opposite-opposite i = refl

opposite-fromℕ< : ∀ a b (lt : a < b) → opposite (fromℕ< (≤-step lt)) ≡ suc (opposite (fromℕ< lt))
opposite-fromℕ< zero .(suc _) (s≤s le) = refl
opposite-fromℕ< (suc a) .(suc _) (s≤s le) rewrite opposite-fromℕ< _ _ le = refl

