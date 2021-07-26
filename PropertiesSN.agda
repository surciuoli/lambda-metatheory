module PropertiesSN where

open import Term
open import Substitution
open import Renaming
open import SN
open import Alpha
open import SubstitutionLemmas
open import SubstitutionCompatibilityLemmas renaming (lemma∼α∙ to subst-comp)
open import Chi
open import IsVar

open import Relation.Binary.PropositionalEquality using (sym; subst₂; refl; trans)
open import Relation.Binary.Core hiding (_⇒_)
open import Data.Product hiding (Σ)
open import Data.Nat
open import Data.Nat.Properties
open import Algebra.Structures
open import Induction.WellFounded
open import Induction.Nat
open import Relation.Nullary

≡⇒α : ∀ {M N} → M ≡ N → M ∼α N
≡⇒α {M} M≡N = subst₂ _∼α_ refl M≡N (∼ρ {M})

m<′m⊔n+1 : ∀ {m n} → m <′ suc (m ⊔ n)
m<′m⊔n+1 {m} {n} = s≤′s (≤⇒≤′ (m≤m⊔n m n))

⊔-comm = IsCommutativeMonoid.comm (IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid ⊔-⊓-0-isCommutativeSemiringWithoutOne)

m<′n⊔m+1 : ∀ {m n} → m <′ suc (n ⊔ m)
m<′n⊔m+1 {m} {n} with n ⊔ m | ⊔-comm n m
m<′n⊔m+1 {m} {n} | .(m ⊔ n) | refl = m<′m⊔n+1 {m} {n}

a≡b→a<′c⊔b+1 : ∀ {a b c} → a ≡ b → a <′ suc (c ⊔ b)
a≡b→a<′c⊔b+1 {a} {.a} {c} refl = m<′n⊔m+1 {a} {c}

a≡b,c≡d→a⊔c+1≡b⊔d+1 : ∀ {a b c d} → a ≡ b → c ≡ d → suc (a ⊔ c) ≡ suc (b ⊔ d)
a≡b,c≡d→a⊔c+1≡b⊔d+1 refl refl = refl

a≡b→a+1≡b+1 : ∀ {a b} → a ≡ b → suc a ≡ suc b
a≡b→a+1≡b+1 refl = refl

a≡b≡c→a+1≡c+1 : ∀ {a b c} → a ≡ c → a ≡ b → suc b ≡ suc c
a≡b≡c→a+1≡c+1 refl refl = refl

a≡b→a+1≤′b+1 : ∀ {a b} → a ≡ b → suc a ≤′ suc b
a≡b→a+1≤′b+1 refl = ≤′-refl

alpha-inversion : ∀ {M N x y} → ƛ x M ∼α ƛ y N → M ∼α N [ y := v x ]
alpha-inversion x = ∼σ (lemma-α-ren (∼σ x))

lemm∼α⇂ : ∀ {M N R} → (x : V) → M ∼α N → (ι ≺+ (x , M)) ∼α (ι ≺+ (x , N)) ⇂ R
lemm∼α⇂ x M∼N y _ with x ≟ y
... | no _ = ∼v
lemm∼α⇂ x M∼N .x _ | yes refl = M∼N

antirenaming  : ∀ {ρ M} → Renaming ρ → (SNMρ : SN (M ∙ ρ)) → Acc _<′_ (height SNMρ) → ∃ λ (SNM : SN M) → height SNMρ ≡ height SNM
antirenamingNe  : ∀ {x ρ M} → Renaming ρ → (SNeMρ : SNe x (M ∙ ρ)) → Acc _<′_ (heightNe SNeMρ) → ∃₂ λ y → λ (SNeM : SNe y M) → heightNe SNeMρ ≡ heightNe SNeM
antirenaming→  : ∀ {ρ M N} → Renaming ρ → (Mρ→N : (M ∙ ρ) →SN N) → Acc _<′_ (height→ Mρ→N) → ∃₂ λ P → λ (M→P : M →SN P) → height→ Mρ→N ≡ height→ M→P × (P ∙ ρ) ∼α N
closureSN/α : ∀ {M N} → (SNM : SN M) → Acc _<′_ (height SNM) → M ∼α N → ∃ λ (SNN : SN N) → height SNN ≡ height SNM
closureSN/αNe : ∀ {x M N} → (SNM : SNe x M) → Acc _<′_ (heightNe SNM) → M ∼α N → ∃ λ (SNN : SNe x N) → heightNe SNN ≡ heightNe SNM
closureSN/α→ : ∀ {M N Q} → (M→N : M →SN N) → Acc _<′_ (height→ M→N) → Q ∼α M → ∃₂ λ P → λ (Q→P : Q →SN P) → height→ Q→P ≡ height→ M→N × P ∼α N

antirenamingNe {x} {ρ} {v y} Renρ _ _ with ρ y | Renρ y 
antirenamingNe {x} {_} {v y} _ (v {.x}) _ | v .x | isVar .x = y , v , refl
antirenamingNe {x} {ρ} {M · N} Renρ (app SNMρ SNNρ) (acc hi) with antirenamingNe {x} {ρ} {M} Renρ SNMρ (hi (heightNe SNMρ) m<′m⊔n+1)
                                                                | antirenaming {ρ} {N} Renρ SNNρ (hi (height SNNρ) (m<′n⊔m+1 {n = heightNe SNMρ}))
... | y , SNM , a≡b | SNN , c≡d = y , app SNM SNN , a≡b,c≡d→a⊔c+1≡b⊔d+1 a≡b c≡d
antirenamingNe {_} {_} {ƛ _ _} Renρ ()
antirenaming {ρ} {v x} Renρ _ _ with ρ x | Renρ x
antirenaming {ρ} {v x} Renρ (sne v) _ | v .y | isVar y = sne v , refl
antirenaming {ρ} {v x} Renρ (exp () _) _ | v .y | isVar y 
antirenaming {ρ} {ƛ x M} Renρ (abs SNMρ) (acc hi) = map abs a≡b→a+1≡b+1 (antirenaming (rename≺+ {x} {χ (ρ , ƛ x M)} Renρ) SNMρ (hi (height SNMρ) ≤′-refl))
antirenaming {ρ} {ƛ x M} Renρ (sne ()) _ 
antirenaming {ρ} {ƛ x M} Renρ (exp () _) _ 
antirenaming {ρ} {M · N} Renρ (sne SNMNρ) (acc hi) = map sne a≡b→a+1≡b+1 (proj₂ (antirenamingNe Renρ SNMNρ (hi (heightNe SNMNρ) ≤′-refl)))
antirenaming {ρ} {M · N} Renρ (exp MNρ→Q SNQ) (acc hi) with antirenaming→ {ρ} {M · N} Renρ MNρ→Q (hi (height→ MNρ→Q) m<′m⊔n+1)
... | P , MN→P , hMNρ→Q≡hMN→P , Pρ∼Q with closureSN/α SNQ (hi (height SNQ) (m<′n⊔m+1 {n = height→ MNρ→Q})) (∼σ Pρ∼Q)
... | SNPρ , hSNPρ≡hSNQ with antirenaming {ρ} {P} Renρ SNPρ (hi (height SNPρ) (a≡b→a<′c⊔b+1 {c = height→ MNρ→Q} hSNPρ≡hSNQ))
... | SNP , hSNPρ≡hSNP = exp MN→P SNP , a≡b,c≡d→a⊔c+1≡b⊔d+1 hMNρ→Q≡hMN→P (trans (sym hSNPρ≡hSNQ) hSNPρ≡hSNP)
antirenaming→ {ρ} {v x} Renρ _ with ρ x | Renρ x
antirenaming→ {ρ} {v x} Renρ () | v .y | isVar y
antirenaming→ {ρ} {ƛ x M} _ ()
antirenaming→ {ρ} {v x · M} Renρ _ with ρ x | Renρ x
antirenaming→ {ρ} {v x · M} Renρ (appl ()) | v .y | isVar y
antirenaming→ {ρ} {ƛ x M · N} Renρ (β .{M ∙ (ρ ≺+ (x , v (χ (ρ , ƛ x M))))}.{N ∙ ρ}.{χ (ρ , ƛ x M)} SNNρ) (acc hi) with antirenaming {ρ} {N} Renρ SNNρ (hi (height SNNρ) ≤′-refl)
... | SNN , hSNNρ≡hSNN = M ∙ (ι ≺+ (x , N)) , β SNN , a≡b→a+1≡b+1 hSNNρ≡hSNN , ∼σ (subst-comp (χ-lemma2 ρ (ƛ x M)))
antirenaming→ {ρ} {(M · N) · R} Renρ (appl .{(M · N) ∙ ρ} Mρ→Q) (acc hi) with antirenaming→ {ρ} {M · N} Renρ Mρ→Q (hi (height→ Mρ→Q) ≤′-refl)
... | P , M→P , hMρ→N≡hM→P , Pρ∼N = P · R , appl M→P , a≡b→a+1≡b+1 hMρ→N≡hM→P , ∼· Pρ∼N ∼ρ 
antirenaming→ {ρ} {(ƛ x M) · N} Renρ (appl ())

closureSN/αNe v _ ∼v = v , refl
closureSN/αNe (app SNM SNN) (acc hi) (∼· M∼P N∼Q) with closureSN/αNe SNM (hi (heightNe SNM) m<′m⊔n+1) M∼P | closureSN/α SNN (hi (height SNN) (m<′n⊔m+1 {n = heightNe SNM})) N∼Q
... | SNP , a≡b | SNQ , c≡d = app SNP SNQ , a≡b,c≡d→a⊔c+1≡b⊔d+1 a≡b c≡d
closureSN/α (sne SNM) (acc hi) M∼N = map sne a≡b→a+1≡b+1 (closureSN/αNe SNM (hi (heightNe SNM) ≤′-refl) M∼N)
closureSN/α (abs SNM) (acc hi) (∼ƛ {_} {N} {x} {y} M∼N z#M z#N) with closureSN/α SNM (hi (height SNM) ≤′-refl) (alpha-inversion (∼ƛ M∼N z#M z#N))
... | SNN[y/x] , hSNN[y/x]≡hSNM = map abs (a≡b≡c→a+1≡c+1 hSNN[y/x]≡hSNM) (antirenaming {M = N} (rename-unary y x) SNN[y/x] (hi (height SNN[y/x]) (a≡b→a+1≤′b+1 hSNN[y/x]≡hSNM)))
closureSN/α (exp M→N SNN) (acc hi) M∼Q with closureSN/α→ M→N (hi (height→ M→N) m<′m⊔n+1) (∼σ M∼Q)
... | P , Q→P , hQ→P≡hM→N , P∼N with closureSN/α SNN (hi (height SNN) (m<′n⊔m+1 {n = height→ M→N})) (∼σ P∼N)
... | SNP , hSNP≡hSNN = (exp Q→P SNP) , a≡b,c≡d→a⊔c+1≡b⊔d+1 hQ→P≡hM→N hSNP≡hSNN
closureSN/α→ (β SNN) (acc hi) (∼· {_} {_} {Q} {N} (∼ƛ {P} {M} {y} {x} {z} z#ƛyP z#ƛxM P[z/y]~M[z/x]) Q∼N) with closureSN/α SNN (hi (height SNN) ≤′-refl) (∼σ Q∼N)
... | SNQ , hSNQ≡hSNN = P ∙ (ι ≺+ (y , Q)) , β SNQ , a≡b→a+1≡b+1 hSNQ≡hSNN , ∼τ (∼τ (≡⇒α (lemma≺+ z#ƛyP)) (lemma-subst P[z/y]~M[z/x] (lemm∼α⇂ z Q∼N))) (∼σ (≡⇒α (lemma≺+ z#ƛxM)))
closureSN/α→ (appl M→N) (acc hi) (∼· {Q} {M} {S} {R} Q∼M S∼R) with closureSN/α→ M→N (hi (height→ M→N) ≤′-refl) Q∼M
... | P , Q→P , hQ→P≡hM→N , P∼N = P · S , appl Q→P , a≡b→a+1≡b+1 hQ→P≡hM→N , ∼· P∼N S∼R

antirenaming′ : ∀ {ρ M} → Renaming ρ → SN (M ∙ ρ) → SN M
antirenaming′ Renρ SNMρ = proj₁ (antirenaming Renρ SNMρ (<-well-founded (height SNMρ)))

closureSN/α′ : ∀ {M N} → SN M → M ∼α N → SN N
closureSN/α′ SNM M∼N = proj₁ (closureSN/α SNM (<-well-founded (height SNM)) M∼N)

renamIm : ∀ {ρ} → Renaming ρ → V → V 
renamIm {ρ} Renρ x with ρ x | Renρ x
... | .(v y) | isVar y = y

renamNe : ∀ {ρ x M} → (ren : Renaming ρ) → SNe x M → SNe (renamIm ren x) (M ∙ ρ)
renam : ∀ {ρ M} → Renaming ρ → SN M → SN (M ∙ ρ)
renam→ : ∀ {ρ M N} → Renaming ρ → M →SN N → Σ[ P ∈ Λ ] (M ∙ ρ →SN P × P ∼α N ∙ ρ)

renamNe {ρ} {x} Renρ v with ρ x | Renρ x
... | .(v y) | isVar y = v {y}
renamNe Renρ (app SNeM SNN) = app (renamNe Renρ SNeM) (renam Renρ SNN)
renam Renρ (sne SNeM) = sne (renamNe Renρ SNeM)
renam {ρ} {ƛ x M} Renρ (abs SNM) = abs (renam (rename≺+ {x} {χ (ρ , ƛ x M)} Renρ) SNM)
renam Renρ (exp M→N SNN) with renam→ Renρ M→N
... | P , Mρ→P , P∼Nρ = exp Mρ→P (closureSN/α′ (renam Renρ SNN) (∼σ P∼Nρ))
renam→ {ρ} {ƛ x M · N} Renρ (β SNN) = let y = χ (ρ , ƛ x M) in (M ∙ ρ ≺+ (x , v y)) ∙ ι ≺+ (y , N ∙ ρ) , β (renam Renρ SNN) , subst-comp (χ-lemma2 ρ (ƛ x M))
renam→ {ρ} Renρ (appl {N = N} M→M′) with renam→ Renρ M→M′
... | P′ , Mρ→P′ , P′≡M′ρ = P′ · (N ∙ ρ) , appl Mρ→P′ , ∼· P′≡M′ρ ∼ρ
