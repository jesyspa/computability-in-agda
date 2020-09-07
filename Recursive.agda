module Recursive where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; pred)
open import Data.Product using (_×_)
open import Data.Fin using (Fin; zero; suc; punchIn; punchOut)
open import Data.Sum using (_⊎_)
open import Data.Vec using (Vec; _∷_; []; lookup) renaming (map to map-Vec)
open import Function using (Bijective)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level renaming (zero to lzero; suc to lsuc)

variable
  n m : ℕ
  b : Bool

data RecFun : (use-mu : Bool) → ℕ → Set where
  Var : Fin n → RecFun b n
  Bind : Vec (RecFun b m) n → RecFun b n → RecFun b m
  Zero : RecFun b 0
  Suc : RecFun b 1
  Rec : RecFun b n → RecFun b (2 + n) → RecFun b (suc n)
  Mu : RecFun b (suc n) → RecFun true n

mutual
  eval-no-mu : Vec ℕ n → RecFun false n → ℕ
  eval-no-mu v (Var i) = lookup v i
  eval-no-mu v (Bind xs r) = eval-no-mu (eval-bindings v xs) r
  eval-no-mu v Zero = zero
  eval-no-mu (x ∷ []) Suc = suc x
  eval-no-mu (x ∷ v) (Rec base rec) = eval-no-mu-rec x v base rec

  eval-bindings : ∀{n m} → Vec ℕ m → Vec (RecFun false m) n → Vec ℕ n
  eval-bindings v [] = []
  eval-bindings v (x ∷ xs) = eval-no-mu v x ∷ eval-bindings v xs

  eval-no-mu-rec : ℕ → Vec ℕ n → RecFun false n → RecFun false (2 + n) → ℕ
  eval-no-mu-rec zero v base rec = eval-no-mu v base
  eval-no-mu-rec (suc k) v base rec = eval-no-mu (k ∷ result ∷ v) rec
    where result = eval-no-mu-rec k v base rec

postulate
  enum-RecFun : ∀ vars → ℕ → RecFun true vars
  enum-RecFun-Surj : ∀ vars → ℕ → Bijective {A = ℕ} {B = RecFun true vars} _≡_ _≡_ (enum-RecFun vars)
  
