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

data IsVar : Λ → Set where
  isv : ∀ {x} → IsVar (v x)

Unary : Σ → V → Λ → Set
Unary σ x M = σ x ≡ M × ∀ {y} → y ≢ x → IsVar (σ y)

postulate unary : ∀ {x M} → Unary (ι ≺+ (x , M)) x M

postulate unary≺+≡ : ∀ {x M N σ} → Unary σ x M → Unary (σ ≺+ (x , N)) x N

postulate unary≺+≢ : ∀ {x y M N σ} → y ≢ x → Unary σ x M → Unary (σ ≺+ (y , N)) x M

postulate unaryv : ∀ {x y z M σ} → Unary σ x (v y) → Unary (σ ≺+ (z , M)) z M

{-Unary : Σ → Λ → Cxt → Type → Set
Unary σ M Γ α = ∀ {x} → IsVar (σ x) ⊎ σ x ≡ M × (Γ ⊢ v x ∶ α)

lemma-Unaryι : ∀ {x α Γ M} → Γ ⊢ M ∶ α → Unary (ι ≺+ (x , M)) M (Γ ‚ x ∶ α) α
lemma-Unaryι {x} M:α {y} with x ≟ y 
lemma-Unaryι {x} M:α .{x} | yes refl = inj₂ (refl , ⊢v (here refl))
... | no _ = inj₁ isv 

lemma-Unary≺+ : ∀ {x z α Γ M σ β} → Unary σ M Γ α → Unary (σ ≺+ (x , v z)) M (Γ ‚ x ∶ β) α
lemma-Unary≺+ {x} {z} Unyσ {y} with x ≟ y
lemma-Unary≺+ {x} {z} Unyσ .{x} | yes refl = inj₁ isv 
... | no x≢y with Unyσ {y}
... | inj₁ isvar = inj₁ isvar
... | inj₂ (refl , Γ⊢y:β) = inj₂ (refl , lemmaWeakening⊢# (#v (sym≢ x≢y)) Γ⊢y:β)

IsVar⇒∃y : (σ : Σ) → (x : V) → IsVar (σ x) → ∃ λ y → σ x ≡ v y
IsVar⇒∃y σ x IsVarσx with σ x
IsVar⇒∃y σ x (isv {y}) | v {.y} = y , refl-}

