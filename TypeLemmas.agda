module TypeLemmas where

open import SoundnessSN
open import Term 
open import Data.Sum

open import Relation.Binary.PropositionalEquality hiding (trans)
open import Induction.WellFounded
open import Data.Unit 

data _ₜ<_ : Type → Type → Set where
  ₜ<l : ∀ {α β} → α ₜ< (α ⟶ β)
  ₜ<r : ∀ {α β} → β ₜ< (α ⟶ β)

wfₜ< : Well-founded _ₜ<_
wfₜ< τ = acc λ y ()
wfₜ< (A ⟶ B) = acc wfₜ<-aux
  where wfₜ<-aux : (γ : Type) → γ ₜ< (A ⟶ B) → Acc _ₜ<_ γ
        wfₜ<-aux .A ₜ<l = wfₜ< A
        wfₜ<-aux .B ₜ<r = wfₜ< B
        
open Transitive-closure _ₜ<_

_ₜ<⁺_ = _<⁺_

wfₜ<⁺ : Well-founded _ₜ<⁺_ 
wfₜ<⁺ = well-founded wfₜ<

lemma-≡Γx : ∀ {α β Γ x} → Γ ⊢ v x ∶ α → Γ ⊢ v x ∶ β → α ≡ β
lemma-≡Γx (⊢v x∈Γ₁) (⊢v x∈Γ₂) = lemma∈!⟨⟩ x∈Γ₁ x∈Γ₂

lemma-ₜ≤ : ∀ {α β Γ M x} → wne x M → Γ ⊢ v x ∶ β → Γ ⊢ M ∶ α → α ₜ<⁺ β ⊎ α ≡ β 
lemma-ₜ≤  nv hdM:β hdM:α = inj₂ (lemma-≡Γx hdM:α hdM:β)
lemma-ₜ≤  {A} {B} (napp M) hdM:β (⊢· M:γ→α _) with lemma-ₜ≤ M hdM:β M:γ→α
... | inj₁ γ→α<β = inj₁ (trans [ ₜ<r ] γ→α<β)
lemma-ₜ≤ {A} .{γ ⟶ A} (napp _) hdM:β (⊢· {γ} M:γ→α _) | inj₂ refl = inj₁ [ ₜ<r ]

lemma-ₜ< : ∀ {α γ β Γ M x} → wne x M → Γ ⊢ v x ∶ β → Γ ⊢ M ∶ α ⟶ γ → α ₜ<⁺ β
lemma-ₜ< M⇓ hdM:β M:α→γ with lemma-ₜ≤ M⇓ hdM:β M:α→γ 
... | inj₁ α→γ<β = trans [ ₜ<l ] α→γ<β
lemma-ₜ< {A} {γ} .{A ⟶ γ} M⇓ hdM:β M:α→γ | inj₂ refl = [ ₜ<l ]
