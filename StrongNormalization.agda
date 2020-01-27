module StrongNormalization where

open import SoundnessSN
open import Term renaming (_⟶_ to _⇒_)
open import Chi
--open import WellFoundnessType
open import Substitution
open import Data.Sum
open import Data.Product hiding (Σ)
open import Beta
open import Alpha
open import SubstitutionLemmas

open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Induction.WellFounded
open import Data.Unit
open import Data.Empty

_ₜ<⁺_ : Type → Type → Set
_ₜ<⁺_ = {!!}

wfₜ<⁺ : Well-founded _ₜ<⁺_
wfₜ<⁺ = {!!}

IsVar : Λ → Set
IsVar (v x) = ⊤
IsVar _ = ⊥

Ren : Σ → Type → Cxt → Set
Ren σ α Γ = ∀ {x} → IsVar (σ x) ⊎ SN (σ x) × (Γ ⊢ v x ∶ α)

SN-lemma-α : ∀ {M N} → SN M → M ∼α N → SN N
SN-lemma-α = {!!}

SN-lemma : ∀ {M Γ α β}
         → Acc _ₜ<⁺_ β
         → SN M
         → Γ ⊢ M ∶ α
         → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Ren σ β Δ → SN (M ∙ σ))
           × (∀ {N} → SN N → Γ ⊢ N ∶ β → (∃ λ γ → α ≡ β ⇒ γ) → SN (M · N)) -- pedir que M . N tipen
           
SN-lemma→ : ∀ {L K σ Γ Δ α B}
          → Acc _ₜ<⁺_ B
          → L →SN K
          → Γ ⊢ L ∶ α
          → σ ∶ Γ ⇀ Δ ⇂ L
          → Ren σ B Δ
          → ∃ λ P → (L ∙ σ) →SN P × P ∼α K ∙ σ
SN-lemma→ {ƛ x L · J} {_} {σ} {Γ} {Δ} accβ (β J⇓) (⊢· _ J:γ) _ Πσ = let z : V
                                                                        z = χ (σ , ƛ x L)
                                                                        L[σ,x=z][z=Jσ]~L[x=J]σ : L [ σ ∣ x := v z ] [ z := J ∙ σ ] ∼α L [ x := J ] ∙ σ
                                                                        L[σ,x=z][z=Jσ]~L[x=J]σ = {!!}
                                                                        σ⇂J : σ ∶ Γ ⇀ Δ ⇂ J
                                                                        σ⇂J = {!!}
                                                                        Jσ⇓ : SN (J ∙ σ)
                                                                        Jσ⇓ = proj₁ (SN-lemma accβ J⇓ J:γ) σ⇂J Πσ
                                                                    in L [ σ ∣ x := v z ] [ z := J ∙ σ ] , β Jσ⇓ , L[σ,x=z][z=Jσ]~L[x=J]σ
SN-lemma→ {L · J} {L' · .J} {σ} {Γ} {Δ} accβ (appl L→L') (⊢· L:γ _) _ Πσ = let σ⇂L : σ ∶ Γ ⇀ Δ ⇂ L
                                                                               σ⇂L = {!!}
                                                                               P , Lσ→P , P~L'σ = SN-lemma→ accβ L→L' L:γ σ⇂L Πσ
                                                                               PJσ~L'Jσ : P · (J ∙ σ) ∼α L' · J ∙ σ 
                                                                               PJσ~L'Jσ = {!!}
                                                                               LJσ→PJσ : L · J ∙ σ →SN P · (J ∙ σ)
                                                                               LJσ→PJσ = appl Lσ→P
                                                                           in P · (J ∙ σ) , LJσ→PJσ , PJσ~L'Jσ
SN-lemmaNe : ∀ {M Γ α β}
           → Acc _ₜ<⁺_ β
           → SNe M
           → Γ ⊢ M ∶ α
           → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Ren σ β Δ → SN (M ∙ σ))
             × (∀ {N} → SN N → Γ ⊢ N ∶ β → (∃ λ γ → α ≡ β ⇒ γ) → SN (M · N))                                                 
SN-lemmaNe .{v x} {Γ} {_} {B} _ (v {x}) _ = thesis₁ , λ N⇓ _ _ → sne (app v N⇓)
  where thesis₁ : ∀ {σ} {Δ} → σ ∶ Γ ⇀ Δ ⇂ (v x) → Ren σ B Δ → SN (v x ∙ σ)
        thesis₁ = {!!}
SN-lemmaNe {P · Q} {Γ} {_} {B} (acc hiₜ) (app P⇓ Q⇓) (⊢· {γ} {ε} P:γ→ε Q:γ) = thesis₁ , λ N⇓ _ _ → sne (app (app P⇓ Q⇓) N⇓)
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ P · Q → Ren σ B Δ → SN (P · Q ∙ σ)
        thesis₁ {σ} {Δ} σ⇂PQ Πσ = let σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
                                      σ⇂P = {!!}
                                      Pσ⇓ : SN (P ∙ σ)
                                      Pσ⇓ = proj₁ (SN-lemmaNe (acc hiₜ) P⇓ P:γ→ε) σ⇂P Πσ
                                      σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
                                      σ⇂Q = {!!}
                                      Qσ⇓ : SN (Q ∙ σ)
                                      Qσ⇓ = proj₁ (SN-lemma (acc hiₜ) Q⇓ Q:γ) σ⇂Q Πσ
                                      γ<β : γ ₜ<⁺ B
                                      γ<β = {!!}
                                      accγ : Acc _ₜ<⁺_ γ
                                      accγ = {!!} --hiₜ γ γ<β
                                      Pσ:γ→ε : Δ ⊢ P ∙ σ ∶ γ ⇒ ε
                                      Pσ:γ→ε = lemma⊢σM P:γ→ε σ⇂P
                                      Qσ:γ : Δ ⊢ Q ∙ σ ∶ γ 
                                      Qσ:γ = {!!}
                                      PQσ⇓ = SN (P · Q ∙ σ)
                                      PQσ⇓ = {!!} --proj₂ (SN-lemma accγ Pσ⇓ Pσ:γ→ε) Qσ⇓ Qσ:γ (ε , refl)
                                  in PQσ⇓
                                  
SN-lemma accβ (sne M⇓) = SN-lemmaNe accβ M⇓ 
SN-lemma {ƛ x P} {Γ} {δ ⇒ ε} {B} accβ (abs P⇓) (⊢ƛ P:ε) = thesis₁ , thesis₂ (⊢ƛ P:ε)
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ ƛ x P → Ren σ B Δ → SN (ƛ x P ∙ σ)
        thesis₁ {σ} {Δ} σ⇂ƛxP Πσ = let z : V
                                       z = χ (σ , ƛ x P)
                                       σ⇂P : (σ ≺+ (x , v z)) ∶ (Γ ‚ x ∶ δ) ⇀ Δ ⇂ P
                                       σ⇂P = {!!}
                                       Πσ,x=z : Ren (σ ≺+ (x , v z)) B Δ
                                       Πσ,x=z = {!!}
                                   in abs (proj₁ (SN-lemma accβ P⇓ P:ε) σ⇂P Πσ,x=z)
        thesis₂ : ∀ {N δ ε} → Γ ⊢ ƛ x P ∶ δ ⇒ ε → SN N → Γ ⊢ N ∶ B → (∃ λ γ → δ ⇒ ε ≡ B ⇒ γ) → SN (ƛ x P · N)
        thesis₂ {N}{.B}{.γ} (⊢ƛ P:γ) N⇓ N:B (γ , refl) = let σ⇂P : (ι ≺+ (x , N)) ∶ (Γ ‚ x ∶ B) ⇀ Γ ⇂ P
                                                             σ⇂P = lemma⇀ (lemmaι≺+⇀ N:B)
                                                             x=N : Ren (ι ≺+ (x ∶ N)) B Γ
                                                             x=N = {!!}
                                                         in exp (β N⇓) (proj₁ (SN-lemma accβ P⇓ P:γ) σ⇂P x=N)
SN-lemma {M} {Γ} {α} {B} accβ (exp {.M}{N} M→N N⇓) M:α = thesis₁ , thesis₂
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Ren σ B Δ → SN (M ∙ σ)
        thesis₁ {σ} {Δ} σ⇂M Πσ = let _ , Mσ→P , P~Nσ = SN-lemma→ accβ M→N M:α σ⇂M Πσ
                                     N:α : Γ ⊢ N ∶ α
                                     N:α = {!!}
                                     σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
                                     σ⇂N = {!!}
                                     Nσ⇓ : SN (N ∙ σ)
                                     Nσ⇓ = proj₁ (SN-lemma accβ N⇓ N:α) σ⇂N Πσ
                                 in exp Mσ→P (SN-lemma-α Nσ⇓ (∼σ P~Nσ))
        thesis₂ : ∀ {P} → SN P → Γ ⊢ P ∶ B → (∃ λ γ → α ≡ B ⇒ γ) → SN (M · P)
        thesis₂ P⇓ P:B α=β→γ = let N:α : Γ ⊢ N ∶ α
                                   N:α = {!!}
                               in exp (appl M→N) (proj₂ (SN-lemma accβ N⇓ N:α) P⇓ P:B α=β→γ)

SN-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → SN M
SN-theo (⊢v _) = sne v
SN-theo (⊢· {α} {B} {M} M:α→β N:α) = proj₂ (SN-lemma (wfₜ<⁺ α) (SN-theo M:α→β) M:α→β) (SN-theo N:α) N:α (B , refl)
SN-theo (⊢ƛ M:α) = abs (SN-theo M:α)

sn-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
sn-theo M:α = sound-SN (SN-theo M:α)
