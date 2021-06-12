module Neutral where

open import Term
open import Chi
open import Substitution
open import Alpha
open import Beta
open import Relation Λ

open import Data.Sum
open import Relation.Binary.PropositionalEquality

-- Weak-neutral

data wne : V → Λ → Set where
  var   : ∀ {x} → wne x (v x)
  app : ∀ {x M N} → wne x M → wne x (M · N)
