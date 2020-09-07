module Enumeration where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; pred; ⌊_/2⌋; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm; +-identityʳ)
open import Data.Nat.Properties using (*-suc; *-assoc; *-comm; *-zeroʳ)
open import Data.Nat.Properties using (≤-step)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin; zero; suc; inject₁; fromℕ; fromℕ<; toℕ; opposite)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ; toℕ-inject₁; fromℕ<-toℕ)
open import Data.Sum using (_⊎_)
open import Function using (Injective; Surjective; Bijective; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; inspect; [_]; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning

record Enumerable (A : Set) : Set where
  field
    enum : ℕ → A
    bijective : Bijective {A = ℕ} {B = A} _≡_ _≡_ enum

open Enumerable

ℕ-Enumerable : Enumerable ℕ
enum ℕ-Enumerable n = n
proj₁ (bijective ℕ-Enumerable) eq = eq
proj₁ (proj₂ (bijective ℕ-Enumerable) y) = y
proj₂ (proj₂ (bijective ℕ-Enumerable) y) = refl

module FinOppositeProperties where
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

  opposite-fromℕ< : ∀ a b (le : a < b) → opposite (fromℕ< (≤-step le)) ≡ suc (opposite (fromℕ< le))
  opposite-fromℕ< zero .(suc _) (s≤s le) = refl
  opposite-fromℕ< (suc a) .(suc _) (s≤s le) rewrite opposite-fromℕ< _ _ le = refl

module NatIteration where
  iterate : {A : Set} → (A → A) → ℕ → A → A
  iterate f zero a = a
  iterate f (suc n) a = f (iterate f n a)

  split-iterate : {A : Set}(f : A → A)(a : A)
                → (n m : ℕ)
                → iterate f (n + m) a ≡ iterate f n (iterate f m a)
  split-iterate f a zero m = refl
  split-iterate f a (suc n) m rewrite split-iterate f a n m = refl


module Diagonal where
  Diagonal : Set
  Diagonal = Σ[ k ∈ ℕ ] Fin (suc k)

  step-Diag : Diagonal → Diagonal
  step-Diag (k , zero) = suc k , fromℕ (suc k)
  step-Diag (k , suc i) = k , inject₁ i

  triangle : ℕ → ℕ
  triangle k = ⌊ suc k * k /2⌋

  open NatIteration

  enum-Diag : ℕ → Diagonal
  enum-Diag n = iterate step-Diag n (zero , zero) 

  code-Diag : Diagonal → ℕ
  code-Diag (k , i) = toℕ (opposite i) + triangle k

  module TriangleProperties where
    elim-⌊/2⌋ : ∀ k i → ⌊ i * 2 + k /2⌋ ≡ i + ⌊ k /2⌋
    elim-⌊/2⌋ k zero = refl
    elim-⌊/2⌋ k (suc i) rewrite elim-⌊/2⌋ k i = refl

    rewrite-triangle : (k : ℕ) → suc (k + suc (k + k * suc k)) ≡ suc k * 2 + (k + k * k)
    rewrite-triangle k
      rewrite *-comm k (suc k)
            | +-suc k (k + (k + k * k))
            | *-comm k 2
            | +-identityʳ k
            | +-assoc k k (k + k * k) = refl

    triangle-relation : ∀ k → triangle (suc k) ≡ suc k + triangle k
    triangle-relation k =
      begin
        ⌊ suc (suc k) * suc k /2⌋
      ≡⟨ cong ⌊_/2⌋ (rewrite-triangle k) ⟩
        ⌊ suc k * 2 + suc k * k /2⌋
      ≡⟨ elim-⌊/2⌋ (suc k * k) (suc k) ⟩
        suc k + ⌊ suc k * k /2⌋
      ∎

  open TriangleProperties
  open FinOppositeProperties

  step-Diag-suc : ∀ d → code-Diag (step-Diag d) ≡ suc (code-Diag d)
  step-Diag-suc (k , zero)
    rewrite opposite-fromℕ k
          | toℕ-fromℕ k
          | triangle-relation k = refl
  step-Diag-suc (k , suc i)
    rewrite opposite-inject₁-suc i
          | toℕ-inject₁ (opposite i) = refl

  code-Diag-LInv : ∀ n → code-Diag (enum-Diag n) ≡ n
  code-Diag-LInv zero = refl
  code-Diag-LInv (suc n) = 
    begin
      code-Diag (step-Diag (enum-Diag n))
    ≡⟨ step-Diag-suc (enum-Diag n) ⟩
      suc (code-Diag (enum-Diag n))
    ≡⟨ cong suc (code-Diag-LInv n) ⟩
      suc n
    ∎

  enum-Diag-Fin-Order : ∀ k i → (lt : i < suc k) → iterate step-Diag i (k , fromℕ k) ≡ (k , opposite (fromℕ< lt))
  enum-Diag-Fin-Order k zero lt = refl
  enum-Diag-Fin-Order k (suc i) (s≤s lt)
    rewrite enum-Diag-Fin-Order k i (≤-step lt)
          | opposite-fromℕ< i k lt = refl

  enum-Diag-Fin : ∀ k (i : Fin (suc k)) → iterate step-Diag (toℕ i) (k , fromℕ k) ≡ (k , opposite i)
  enum-Diag-Fin k i =
    begin
      iterate step-Diag (toℕ i) (k , fromℕ k)
    ≡⟨ enum-Diag-Fin-Order k (toℕ i) (toℕ<n i)⟩
      (k , opposite (fromℕ< (toℕ<n i)))
    ≡⟨ cong (λ e → k , opposite e) (fromℕ<-toℕ i (toℕ<n i)) ⟩
      (k , opposite i)
    ∎

  enum-Diag-triangle : ∀ k → enum-Diag (triangle k) ≡ (k , fromℕ k)
  enum-Diag-triangle zero = refl
  enum-Diag-triangle (suc k) =
    begin
      enum-Diag (triangle (suc k))
    ≡⟨ cong enum-Diag (triangle-relation k) ⟩
      enum-Diag (suc k + triangle k)
    ≡⟨ split-iterate step-Diag (zero , zero) (suc k) (triangle k) ⟩
      iterate step-Diag (suc k) (enum-Diag (triangle k))
    ≡⟨ cong (iterate step-Diag (suc k)) (enum-Diag-triangle k) ⟩
      iterate step-Diag (suc k) (k , fromℕ k)
    ≡⟨ sym (cong (λ e → iterate step-Diag (suc e) (k , fromℕ k)) (toℕ-fromℕ k)) ⟩
      iterate step-Diag (suc (toℕ (fromℕ k))) (k , fromℕ k)
    ≡⟨ cong step-Diag (enum-Diag-Fin k (fromℕ k)) ⟩
      step-Diag (k , opposite (fromℕ k))
    ≡⟨ cong (λ e → step-Diag (k , e)) (opposite-fromℕ k) ⟩
      step-Diag (k , zero)
    ∎

  code-Diag-RInv : ∀ d → enum-Diag (code-Diag d) ≡ d
  code-Diag-RInv (k , i) =
    begin
      enum-Diag (toℕ (opposite i) + triangle k)
    ≡⟨ split-iterate step-Diag (zero , zero) (toℕ (opposite i)) (triangle k) ⟩
      iterate step-Diag (toℕ (opposite i)) (enum-Diag (triangle k))
    ≡⟨ cong (iterate step-Diag (toℕ (opposite i))) (enum-Diag-triangle k) ⟩
      iterate step-Diag (toℕ (opposite i)) (k , fromℕ k)
    ≡⟨ enum-Diag-Fin k (opposite i) ⟩
      k , opposite (opposite i)
    ≡⟨ cong (λ e → k , e) (opposite-opposite i) ⟩
      k , i
    ∎

  Diag-Enumerable : Enumerable Diagonal
  enum Diag-Enumerable = enum-Diag
  proj₁ (bijective Diag-Enumerable) {x = n₀} {y = n₁} eq =
    begin
      n₀
    ≡⟨ sym (code-Diag-LInv n₀) ⟩
      code-Diag (enum-Diag n₀)
    ≡⟨ cong code-Diag eq ⟩
      code-Diag (enum-Diag n₁)
    ≡⟨ code-Diag-LInv n₁ ⟩
      n₁
    ∎
  proj₁ (proj₂ (bijective Diag-Enumerable) d) = code-Diag d
  proj₂ (proj₂ (bijective Diag-Enumerable) d) = code-Diag-RInv d

ℕ²-Enumerable : Enumerable (ℕ × ℕ)
enum ℕ²-Enumerable n = ?
proj₁ (bijective ℕ²-Enumerable) = ?
proj₂ (bijective ℕ²-Enumerable) y = ?
