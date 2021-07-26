module Renaming where

open import Term
open import Substitution
open import Chi
open import IsVar

open import Data.Product hiding (Σ)
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  
Renaming : Σ → Set
Renaming ρ = (x : V) → IsVar (ρ x)

renameι : Renaming ι
renameι x = isVar x

rename≺+ : ∀ {x y ρ} → Renaming ρ → Renaming (ρ ≺+ (x , v y))
rename≺+ {x} {y} Renρ z with x ≟ z
... | no _ = Renρ z
rename≺+ {.z} {y} Renρ z | yes refl = isVar y

rename-unary : (x y : V) → Renaming (ι ≺+ (x , v y))
rename-unary x y = rename≺+ {x} {y} renameι
