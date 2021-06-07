module SN where

open import Chi
open import Term renaming (_⟶_ to _⇒_) hiding (_∶_)
open import Substitution hiding (_∘_)

open import Data.Product hiding (Σ)
open import Data.Nat

infix 4 _→SN_

data SN : Λ → Set
data SNe : V → Λ → Set 
data _→SN_ : Λ → Λ → Set

data _→SN_ where
  β    : ∀ {M N x} → SN N → ƛ x M · N →SN M ∙ (ι ≺+ (x , N))
  appl : ∀ {M M' N} → M →SN M' → M · N →SN M' · N

data SNe where
  v   : ∀ {x} → SNe x (v x)
  app : ∀ {x M N} → SNe x M → SN N → SNe x (M · N)

data SN where
  sne   : ∀ {M x} → SNe x M → SN M 
  abs  : ∀ {M x} → SN M → SN (ƛ x M) 
  exp : ∀ {M N} → M →SN N → SN N → SN M

height→  : ∀ {M N} → M →SN N → ℕ
heightNe : ∀ {M x} → SNe x M → ℕ
height   : ∀ {M} → SN M → ℕ

height→ (β N⇓) = suc (height N⇓)
height→ (appl M→N) = suc (height→ M→N)
heightNe v = 0
heightNe (app M⇓ N⇓) = suc (heightNe M⇓ ⊔ height N⇓)
height (abs M⇓) = suc (height M⇓)
height (sne M⇓) = suc (heightNe M⇓)
height (exp M→N N⇓) = suc (height→ M→N ⊔ height N⇓)
