module Unary where

open import Chi
open import Term
open import Substitution
open import ListProperties

open import Data.Nat
open import Data.Sum
open import Data.Product hiding (Σ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty

data IsVar : Λ → Set where
  isv : ∀ {x} → IsVar (v x)

Unary : Σ → V → Λ → Set
Unary σ x M = σ x ≡ M × ∀ {y} → y ≢ x → IsVar (σ y)

unary : ∀ {x M} → Unary (ι ≺+ (x , M)) x M
unary {x} {M} with x ≟ x
... | no x≢x = ⊥-elim (x≢x refl)
... | yes refl = refl , aux
  where aux : {y : V} → y ≢ x → IsVar ((ι ≺+ (x , M)) y)
        aux {y} _ with x ≟ y
        ... | no _ = isv
        aux {.x} y≢x | yes refl = ⊥-elim (y≢x refl)

unary≺+≡ : ∀ {x y σ M} → Unary σ x M → Unary (σ ≺+ (x , v y)) x (v y)
unary≺+≡ {x} {y} {σ} Unyσ with x ≟ x
... | no x≢x = ⊥-elim (x≢x refl)
... | yes _ = refl , aux
  where aux : {z : V} → z ≢ x → IsVar ((σ ≺+ (x , v y)) z)
        aux {z} z≢x with x ≟ z
        ... | no _ = proj₂ Unyσ z≢x
        aux {.x} z≢x | yes refl = ⊥-elim (z≢x refl)

unary≺+≢ : ∀ {x y z σ M} → y ≢ x → Unary σ x M → Unary (σ ≺+ (y , v z)) x M
unary≺+≢ {x} {y} {z} {σ} y≢x Unyσ with y ≟ x
... | yes y≡x = ⊥-elim (y≢x y≡x)
... | no _ = proj₁ Unyσ , aux
  where aux : {w : V} → w ≢ x → IsVar ((σ ≺+ (y , v z)) w)
        aux {w} w≢x with y ≟ w
        ... | no _ = proj₂ Unyσ w≢x
        aux {.y} _ | yes refl = isv

unaryv : ∀ {x y z M σ} → Unary σ x (v y) → Unary (σ ≺+ (z , M)) z M
unaryv = ?
{-uanryv {x} {y} {z} Unyσ with z ≟ z
... | no z≢z = ⊥-elim (z≢z refl)
... | yes _ = aux
  where aux : {w : V} → -}

