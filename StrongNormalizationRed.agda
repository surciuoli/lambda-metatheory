module StrongNormalizationRed where

open import Term
open import SN renaming (β to βSN)
open import SoundnessSN renaming (β to βSN)
open import Renaming
open import PropertiesSN
open import SubstitutionLemmas
open import Alpha
open import Beta
open import Relation hiding (_⊆_;refl;_++_)
open import Chi
open import Substitution
open import ListProperties

open import Data.Product hiding (Σ)
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_*_)
open import Relation.Nullary
open import Data.Empty
open import Data.List
open import Data.List.Any as Any 
open Any.Membership-≡ renaming (_∈_ to _∈l_; _∉_ to _∉l_) hiding (_⊆_)

Red : Λ → Cxt → Type → Set
Red M Γ τ = (Γ ⊢ M ∶ τ) × SN M
Red M Γ (α ⟶ β) = ∀ {Δ N} → Γ ⊆ Δ → Δ ⊢ N ∶ α → Red N Δ α → Red (M · N) Δ β

closure-Red/α : ∀ {α M N Γ} → M ∼α N → Red M Γ α → Red N Γ α
closure-Red/α {τ} M∼N (M:τ , M⇓) = lemma⊢α M:τ M∼N , closureSN/α′ M⇓ M∼N
closure-Red/α {α ⟶ β} {M} {N} M∼N RedPα→RedMPβ = λ {Δ} {P} Γ⊆Δ P:α RedPα → closure-Red/α (∼· M∼N ∼ρ) (RedPα→RedMPβ Γ⊆Δ P:α RedPα)

Red⊆ : ∀ {α Γ Δ M} → Γ ⊆ Δ → Red M Γ α → Red M Δ α
Red⊆ {τ} Γ⊆Δ (M:τ , SNM) = (lemmaWeakening⊢ Γ⊆Δ M:τ , SNM)
Red⊆ {α ⟶ β} Γ⊆Δ RedN→RedMN Δ⊆E N:α RedN = RedN→RedMN (τ⊆ Γ⊆Δ Δ⊆E) N:α RedN

→SN⇒→α* : ∀ {M N} → M →SN N → M →α* N
→SN⇒→α* (βSN _)  = just (inj₁ (ctxinj ▹β))
→SN⇒→α* (appl M→M') = app-star-l (→SN⇒→α* M→M')

extensionality : ∀ {x M} → SN (M · v x) → SN M
extensionality (sne (app SNM _)) = sne SNM
extensionality {x} (exp (βSN {x = y} _) SNM[x/y]) = abs (antirenaming′ (rename-unary y x) SNM[x/y])
extensionality {x} (exp (appl M→N) SNNx) = exp M→N (extensionality SNNx)

_∉_ : V → Cxt → Set
x ∉ Γ = ¬ (x ∈ Γ)

Γ⊆Γ,x : ∀ {x Γ α} → x ∉ Γ → Γ ⊆ Γ ‚ x ∶ α
Γ⊆Γ,x {x} x∉Γ {y} y∈Γ with y ≟ x
... | no y≠x = there y≠x y∈Γ , refl
Γ⊆Γ,x {x} x∉Γ {.x} x∈Γ | yes refl = ⊥-elim (x∉Γ x∈Γ)

last-v : ∀ {Γ x α} → Γ ‚ x ∶ α ⊢ v x ∶ α
last-v = ⊢v (here refl)

ξ : Λ → Cxt → V
ξ M Γ = χ' (fv M ++ dom Γ)

ξ-lemma₁ : (M : Λ)(Γ : Cxt) → ξ M Γ # M
ξ-lemma₁ M Γ = lemma∉fv→# (c∉xs++ys→c∉xs (lemmaχ∉ (fv M ++ dom Γ)))

x∈Γ→x∈domΓ : ∀ {x Γ} → x ∈ Γ → x ∈l dom Γ
x∈Γ→x∈domΓ (here refl) = here refl
x∈Γ→x∈domΓ (there _ x∈Γ') = there (x∈Γ→x∈domΓ x∈Γ')

x∉domΓ→x∉Γ : ∀ {x Γ} → x ∉l dom Γ → x ∉ Γ
x∉domΓ→x∉Γ x∉domΓ = λ x∈Γ → ⊥-elim (x∉domΓ (x∈Γ→x∈domΓ x∈Γ))

ξ-lemma₂ : (M : Λ)(Γ : Cxt) → ξ M Γ ∉ Γ
ξ-lemma₂ M Γ = x∉domΓ→x∉Γ (c∉xs++ys→c∉ys {xs = fv M} (lemmaχ∉ (fv M ++ dom Γ)))

lemma-≡Γx : ∀ {α β Γ x} → Γ ⊢ v x ∶ α → Γ ⊢ v x ∶ β → α ≡ β
lemma-≡Γx (⊢v x∈Γ₁) (⊢v x∈Γ₂) = lemma∈!⟨⟩ x∈Γ₁ x∈Γ₂

CR1 : ∀ {α Γ M} → Red M Γ α → (Γ ⊢ M ∶ α) × SN M 
CR2 : ∀ {α Γ M N} → Γ ⊢ M ∶ α → M →SN N → Red N Γ α → Red M Γ α
CR3 : ∀ {α Γ M x} → Γ ⊢ M ∶ α → SNe x M → Red M Γ α

CR1 {τ} p = p
CR1 {α ⟶ β} {Γ} {M} RedNα→RedMNβ with CR1 {β} {Γ ‚ ξ M Γ ∶ α} (RedNα→RedMNβ (Γ⊆Γ,x (ξ-lemma₂ M Γ)) last-v (CR3 {α} last-v v))
... | (⊢· Γ,x:α⊢M:α'⟶β Γ,x:α⊢x:α') , Mx⇓ with lemma-≡Γx Γ,x:α⊢x:α' last-v
... | refl = lemmaStrengthening⊢# (ξ-lemma₁ M Γ) Γ,x:α⊢M:α'⟶β , extensionality Mx⇓
CR2 {τ} M:τ M→N (N:τ , N⇓) = (M:τ , exp M→N N⇓)
CR2 {α ⟶ β} {Γ} {M} {N} M:α⟶β M→N RedPα→RedNPβ =
  λ {Δ} {P} Γ⊆Δ P:α RedPα → CR2 (⊢· (lemmaWeakening⊢ Γ⊆Δ M:α⟶β) P:α) (appl M→N) (RedPα→RedNPβ Γ⊆Δ P:α RedPα)
CR3 {τ} M:α M⇓ = (M:α , sne M⇓)
CR3 {α ⟶ β} M:α⟶β M⇓ = λ {Δ} {N} Γ⊆Δ N:α RedNα → CR3 (⊢· (lemmaWeakening⊢ Γ⊆Δ M:α⟶β) N:α) (app M⇓ (proj₂ (CR1 RedNα)))

-- REDUCIBLE SUBSTITUTIONS

_∶_⇀Red_⇂_ : Σ → Cxt → Cxt → Λ → Set
σ ∶ Γ ⇀Red Δ ⇂ M = ∀ {x} → x * M → (x∈Γ : x ∈ Γ) → Red (σ x) Δ (Γ ⟨ x∈Γ ⟩)

red-subst→typed : ∀ {σ Γ Δ M} → σ ∶ Γ ⇀Red Δ ⇂ M → σ ∶ Γ ⇀ Δ ⇂ M
red-subst→typed σ∶Γ⇀Δ x*M x∈Γ = proj₁ (CR1 (σ∶Γ⇀Δ x*M x∈Γ))

⇀Red≺+ :  ∀ {α Γ x N σ Δ M} → Red N Δ α → σ ∶ Γ ⇀Red Δ ⇂ ƛ x M → (σ ≺+ (x , N)) ∶ (Γ ‚ x ∶ α) ⇀Red Δ ⇂ M
⇀Red≺+ {α} {Γ} {x} RedNα σ:Γ⇀Δ⇂ƛxM {y} y*M y∈Γ,x with x ≟ y
... | no x≠y with y∈Γ,x
...   | here x=y = ⊥-elim (x≠y (sym x=y))
...   | there _ y∈Γ = σ:Γ⇀Δ⇂ƛxM (*ƛ y*M x≠y) y∈Γ
⇀Red≺+ {α} {Γ} {x} RedNα σ:Γ⇀Δ {y} _ (there y≠x _) | yes x=y = ⊥-elim (y≠x (sym x=y))
⇀Red≺+ {α} {Γ} {x} RedNα σ:Γ⇀Δ {.x} _ (here refl) | yes refl = RedNα

⇀Redι : ∀ {Γ M} → ι ∶ Γ ⇀Red Γ ⇂ M
⇀Redι _ x∈Γ = CR3 (⊢v x∈Γ) v

⇀Red⊆ : ∀ {σ Γ Δ E M} → Δ ⊆ E → σ ∶ Γ ⇀Red Δ ⇂ M → σ ∶ Γ ⇀Red E ⇂ M
⇀Red⊆ Δ⊆E σ:Γ⇀Δ x*M x∈Γ = Red⊆ Δ⊆E (σ:Γ⇀Δ x*M x∈Γ)

⇀Red· : ∀ {σ M N Γ Δ} → σ ∶ Γ ⇀Red Δ ⇂ (M · N) → (σ ∶ Γ ⇀Red Δ ⇂ M) × (σ ∶ Γ ⇀Red Δ ⇂ N)
⇀Red· σ:Γ⇀Δ⇂MN = (λ x*M → σ:Γ⇀Δ⇂MN (*·l x*M)) , (λ x*N → σ:Γ⇀Δ⇂MN (*·r x*N))

-- SUBSTITUTION LEMMA

subst-lemma : ∀ {σ Γ Δ M α} → Γ ⊢ M ∶ α → σ ∶ Γ ⇀Red Δ ⇂ M → Red (M ∙ σ) Δ α
subst-lemma (⊢v x∈Γ) σ:Γ⇀Δ = σ:Γ⇀Δ *v x∈Γ
subst-lemma (⊢· M:α⟶β N:α) σ:Γ⇀Δ =
  subst-lemma M:α⟶β (proj₁ (⇀Red· σ:Γ⇀Δ)) ρ⊆ (lemma⊢σM N:α (red-subst→typed (proj₂ (⇀Red· σ:Γ⇀Δ)))) (subst-lemma N:α (proj₂ (⇀Red· σ:Γ⇀Δ)))
subst-lemma {σ} {Γ} {Δ} {ƛ x M} {α ⟶ β} (⊢ƛ M:β) σ:Γ⇀Δ⇂ƛxM {E} {N} Δ⊆E N:α RedN =
  let RedMσ,x=N = subst-lemma M:β (⇀Red≺+ RedN (⇀Red⊆ Δ⊆E σ:Γ⇀Δ⇂ƛxM))
      RedMσ,x=y,y=N = closure-Red/α (∼σ (corollary1SubstLemma (χ-lemma2 σ (ƛ x M)))) RedMσ,x=N
      ƛxMσN→Mσ,x=y,y=N = βSN (proj₂ (CR1 RedN))
      ƛxMσ:α⟶β = lemma⊢σM (⊢ƛ M:β) (red-subst→typed σ:Γ⇀Δ⇂ƛxM)
      ƛxMσN→Mσ,x=y,y=N:β = ⊢· (lemmaWeakening⊢ Δ⊆E ƛxMσ:α⟶β) N:α
  in CR2 ƛxMσN→Mσ,x=y,y=N:β ƛxMσN→Mσ,x=y,y=N RedMσ,x=y,y=N

theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → Red M Γ α
theo M:α = closure-Red/α (∼σ lemma∙ι) (subst-lemma M:α ⇀Redι)

coro : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
coro M:α = sound-SN (proj₂ (CR1 (theo M:α)))
