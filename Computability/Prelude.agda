module Computability.Prelude where

open import Data.Bool public using (Bool; false; true)
open import Data.Empty public using (⊥; ⊥-elim)
open import Data.Nat public using (ℕ; zero; suc; _+_; _*_)
open import Data.Product public using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum public using (_⊎_)
open import Data.Unit public using (⊤)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)
open import Level public using (Level) renaming (zero to lzero; suc to lsuc)

