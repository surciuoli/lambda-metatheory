module UnaryB where

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

Unary : Σ → Λ → Cxt → Type → Set
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
IsVar⇒∃y σ x (isv {y}) | v {.y} = y , refl
