module IsVar where

open import Chi using (V)
open import Term using (Λ; v)

data IsVar : Λ → Set where
  isVar : (x : V) → IsVar (v x)
