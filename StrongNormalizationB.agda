module StrongNormalizationB where

open import SN
open import SoundnessSN
open import Term renaming (_⟶_ to _⇒_)
open import Chi
open import Substitution
open import Data.Sum
open import Data.Product hiding (Σ)
open import Beta
open import Alpha
open import SubstitutionLemmas
open import ListProperties
open import Relation using (just; trans)
open import UnaryB
open import TypeLemmas
open import SubstitutionCompatibilityLemmas
open import PropertiesSN

open import Data.Nat hiding (_*_)
open import Relation.Binary.PropositionalEquality renaming (trans to trans≡)
open import Induction.WellFounded
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Relation.Nullary
open import Induction.Nat
open import Data.Nat.Properties
open import Relation.Binary hiding (_⇒_)
open import Algebra.Structures

-- Well-foundness proofs

open Lexicographic _ₜ<⁺_ (λ _ m n → m <′ n) renaming (_<_ to _ₜ,ₙ<_ ; well-founded to wfΣ)

wfₜ,ₙ< : Well-founded _ₜ,ₙ<_
wfₜ,ₙ< = wfΣ wfₜ<⁺ <-well-founded

-- Auxiliary lemmas

x→M⇒⊥ : ∀ {x M} → v x →SN M → ⊥
x→M⇒⊥ ()

xM→N⇒⊥ : ∀ {x M N} → v x · M →SN N → ⊥
xM→N⇒⊥ (appl ()) 

SNe-preservedby-σ→SN : ∀ {σ x M N} → SNe x M → IsVar (σ x) → M ∙ σ →SN N → ⊥
SNe-preservedby-σ→SN {σ} {x} v isvarσx xσ→N with σ x
SNe-preservedby-σ→SN {σ} {x} v (isv {y}) y→M | v .y = ⊥-elim (x→M⇒⊥ y→M)
SNe-preservedby-σ→SN {σ} {x} (app v _) isvarσx xPσ→N with σ x
SNe-preservedby-σ→SN {σ} {x} (app v _) (isv {y}) yPσ→N | v .y = ⊥-elim (xM→N⇒⊥ yPσ→N)
SNe-preservedby-σ→SN {σ} {x} (app P⇓ Q⇓) isvarσx (appl Pσ→R) = SNe-preservedby-σ→SN P⇓ isvarσx Pσ→R

SNe-preservedby-σ : ∀ {σ x M} → SNe x M → IsVar (σ x) → SN (M ∙ σ) → ∃ λ y → SNe y (M ∙ σ)
SNe-preservedby-σ {σ} {x} v isvarσx xσ⇓ with σ x
SNe-preservedby-σ {σ} {x} v (isv {.y}) (sne (v {.y})) | v y = y , v
SNe-preservedby-σ {σ} {x} v (isv {.y}) (exp y→M _) | v y = ⊥-elim (SNe-preservedby-σ→SN (v {x}) (isv {y}) y→M)
SNe-preservedby-σ {σ} {x} (app P⇓ Q⇓) _ (sne (app {y} Pσ⇓ Qσ⇓)) = y , app Pσ⇓ Qσ⇓ 
SNe-preservedby-σ {σ} {x} (app P⇓ Q⇓) isvarσx (exp PQσ→M _) = ⊥-elim (SNe-preservedby-σ→SN (app P⇓ Q⇓) isvarσx PQσ→M)

→SN⊂→α : ∀ {M N} → M →SN N → M →α* N
→SN⊂→α (β _)  = just (inj₁ (ctxinj ▹β))
→SN⊂→α (appl M→M') = app-star-l (→SN⊂→α M→M')

lemmaσ⇂· : ∀ {σ Γ Δ P Q} → σ ∶ Γ ⇀ Δ ⇂ P · Q → (σ ∶ Γ ⇀ Δ ⇂ P) × (σ ∶ Γ ⇀ Δ ⇂ Q)
lemmaσ⇂· σ⇂PQ = (λ x*P → σ⇂PQ (*·l x*P)) , (λ x*Q → σ⇂PQ (*·r x*Q))

-- Main lemma

SN-lemma : ∀ {M Γ α β N}
         → (M⇓ : SN M)
         → Acc _ₜ,ₙ<_ (β , height M⇓)
         → Γ ⊢ M ∶ α
         → SN N
         → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ N Γ β → SN (M ∙ σ))
           × ((∃ λ γ → α ≡ β ⇒ γ) → Γ ⊢ N ∶ β → SN (M · N)) 

SN-lemma→ : ∀ {M N σ Γ Δ α β P}
          → (M→N : M →SN N)
          → Acc _ₜ,ₙ<_ (β , height→ M→N)
          → Γ ⊢ M ∶ α
          → SN P            
          → σ ∶ Γ ⇀ Δ ⇂ M        
          → Unary σ P Γ β
          → ∃ λ Q → (M ∙ σ) →SN Q × Q ∼α N ∙ σ

SN-lemmaNe : ∀ {M Γ α β x N}
           → (M⇓ : SNe x M)
           → Acc _ₜ,ₙ<_ (β , heightNe M⇓)
           → Γ ⊢ M ∶ α
           → SN N
           → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ N Γ β → SN (M ∙ σ))
             × ((∃ λ γ → α ≡ β ⇒ γ) → Γ ⊢ N ∶ β → SN (M · N)) 

SN-lemma→ {ƛ x L · J} {_} {σ} {Γ} {Δ} {α} {B} (β J⇓) (acc hi) (⊢· _ J:γ) P⇓ σ⇂ƛxLJ Unyσ =
  let z : V
      z = χ (σ , ƛ x L)
      L[σ,x=z][z=Jσ]~L[x=J]σ : L [ σ ∣ x := v z ] [ z := J ∙ σ ] ∼α L [ x := J ] ∙ σ
      L[σ,x=z][z=Jσ]~L[x=J]σ = lemma∼α∙ (χ-lemma2 σ (ƛ x L))
      σ⇂J : σ ∶ Γ ⇀ Δ ⇂ J
      σ⇂J = proj₂ (lemmaσ⇂· σ⇂ƛxLJ)
      Jσ⇓ : SN (J ∙ σ)
      Jσ⇓ = proj₁ (SN-lemma J⇓ (hi (B , height J⇓) (right ≤′-refl)) J:γ P⇓) σ⇂J Unyσ
  in L [ σ ∣ x := v z ] [ z := J ∙ σ ] , β Jσ⇓ , L[σ,x=z][z=Jσ]~L[x=J]σ
SN-lemma→ {L · J} {L' · .J} {σ} {Γ} {Δ} {_} {B} (appl L→L') (acc hi) (⊢· L:γ _) P⇓ σ⇂LJ Unyσ =
  let σ⇂L : σ ∶ Γ ⇀ Δ ⇂ L
      σ⇂L = proj₁ (lemmaσ⇂· σ⇂LJ)
      P , Lσ→P , P~L'σ = SN-lemma→ L→L' (hi (B , height→ L→L') (right ≤′-refl)) L:γ P⇓ σ⇂L Unyσ
      PJσ~L'Jσ : P · (J ∙ σ) ∼α L' · J ∙ σ 
      PJσ~L'Jσ = ∼· P~L'σ ∼ρ
      LJσ→PJσ : L · J ∙ σ →SN P · (J ∙ σ)
      LJσ→PJσ = appl Lσ→P
  in P · (J ∙ σ) , LJσ→PJσ , PJσ~L'Jσ

SN-lemmaNe .{v x} {Γ} {_} {B} {.x} {N} (v {x}) _ _ N⇓  = thesis₁ , λ _ _ → sne (app v N⇓)
  where thesis₁ : ∀ {σ} {Δ} → σ ∶ Γ ⇀ Δ ⇂ (v x) → Unary σ N Γ B → SN (v x ∙ σ)
        thesis₁ {σ} _ Unyσ with σ x | Unyσ {x} 
        ... | .(v y) | inj₁ (isv {y}) = sne v
        ... | _ | inj₂ (refl , _) = N⇓ 
SN-lemmaNe {P · Q} {Γ} {_} {B} {.x} {N} (app {x} P⇓ Q⇓) (acc hi) (⊢· {γ} {ε} P:γ→ε Q:γ) N⇓ =
  thesis₁ , λ _ _ → sne (app (app P⇓ Q⇓) N⇓)
    where
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ P · Q → Unary σ N Γ B → SN (P · Q ∙ σ)
        thesis₁ {σ} {Δ} σ⇂PQ Unyσ =
          let m , n = heightNe P⇓ , height Q⇓
              σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
              σ⇂P = λ x*P → σ⇂PQ (*·l x*P)
              Pσ⇓ : SN (P ∙ σ)
              Pσ⇓ = proj₁ (SN-lemmaNe P⇓ (hi (B , m) (right (m<′m⊔n+1 {m} {n}))) P:γ→ε N⇓) σ⇂P Unyσ
              σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
              σ⇂Q = λ x*Q → σ⇂PQ (*·r x*Q)
              Qσ⇓ : SN (Q ∙ σ)
              Qσ⇓ = proj₁ (SN-lemma Q⇓ (hi (B , n) (right (m<′n⊔m+1 {n} {m}))) Q:γ N⇓) σ⇂Q Unyσ
              Pσ:γ→ε : Δ ⊢ P ∙ σ ∶ γ ⇒ ε
              Pσ:γ→ε = lemma⊢σM P:γ→ε σ⇂P                                                                            
              Qσ:γ : Δ ⊢ Q ∙ σ ∶ γ 
              Qσ:γ = lemma⊢σM Q:γ σ⇂Q
              PQσ⇓₁ = λ isvσx → sne (app (proj₂ (SNe-preservedby-σ {σ} {x} {P} P⇓ isvσx Pσ⇓)) Qσ⇓)
              PQσ⇓₂ = λ { (_ , Γ⊢x:B) →
                let γ<β : γ ₜ<⁺ B
                    γ<β = lemma-ₜ< (lemma-ne P⇓) Γ⊢x:B P:γ→ε
                in proj₂ (SN-lemma Pσ⇓ (hi (γ , height Pσ⇓) (left γ<β)) Pσ:γ→ε Qσ⇓) (ε , refl) Qσ:γ }
          in [ PQσ⇓₁ , PQσ⇓₂ ]′ (Unyσ {x})
                                  
SN-lemma {β = B} (sne M⇓) (acc hi) = SN-lemmaNe M⇓ (hi (B , heightNe M⇓) (right ≤′-refl))
SN-lemma {ƛ x P} {Γ} {δ ⇒ ε} {B} {N} (abs P⇓) (acc hi) (⊢ƛ P:ε) N⇓ = thesis₁ , thesis₂ (⊢ƛ P:ε)
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ ƛ x P → Unary σ N Γ B → SN (ƛ x P ∙ σ)
        thesis₁ {σ} {Δ} σ⇂ƛxP Unyσ =
          let z : V
              z = χ (σ , ƛ x P)
              σ⇂P : (σ ≺+ (x , v z)) ∶ (Γ ‚ x ∶ δ) ⇀ (Δ ‚ z ∶ δ) ⇂ P
              σ⇂P = lemmaaux⇀ (χ-lemma2 σ (ƛ x P)) σ⇂ƛxP
              Unyσ,x=z : Unary (σ ≺+ (x , v z)) N (Γ ‚ x ∶ δ) B
              Unyσ,x=z = lemma-Unary≺+ Unyσ
              Pσ,x=z⇓ = proj₁ (SN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:ε N⇓) σ⇂P Unyσ,x=z
          in abs Pσ,x=z⇓
        thesis₂ : ∀ {δ ε} → Γ ⊢ ƛ x P ∶ δ ⇒ ε → (∃ λ γ → δ ⇒ ε ≡ B ⇒ γ) → Γ ⊢ N ∶ B → SN (ƛ x P · N)
        thesis₂ {.B} {.γ} (⊢ƛ P:γ) (γ , refl) N:B =
          let x=N⇂P : (ι ≺+ (x , N)) ∶ (Γ ‚ x ∶ B) ⇀ Γ ⇂ P
              x=N⇂P = lemma⇀ (lemmaι≺+⇀ N:B)
              Unyx=N : Unary (ι ≺+ (x , N)) N (Γ ‚ x ∶ B) B
              Unyx=N = lemma-Unaryι N:B
              Px=N⇓ = proj₁ (SN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:γ N⇓) x=N⇂P Unyx=N
          in exp (β N⇓) Px=N⇓
SN-lemma {M} {Γ} {α} {B} {P} (exp {.M} {N} M→N N⇓) (acc hi) M:α P⇓ = thesis₁ , thesis₂
  where m = height→ M→N
        n = height N⇓ 
        M→αN : M →α* N
        M→αN = →SN⊂→α M→N
        N:α : Γ ⊢ N ∶ α
        N:α = lemma⊢→α* M:α M→αN
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ P Γ B → SN (M ∙ σ)
        thesis₁ {σ} {Δ} σ⇂M Unyσ =
          let _ , Mσ→P , P∼Nσ = SN-lemma→ M→N (hi (B , m) (right (m<′m⊔n+1 {m} {n}))) M:α P⇓ σ⇂M Unyσ
              σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
              σ⇂N = λ x*N → σ⇂M ((dual-#-* lemma→α*#) x*N M→αN)
              Nσ⇓ : SN (N ∙ σ)
              Nσ⇓ = proj₁ (SN-lemma N⇓ (hi (B , n) (right (m<′n⊔m+1 {n} {m}))) N:α P⇓) σ⇂N Unyσ
          in exp Mσ→P (closureSN/α′ Nσ⇓ (∼σ P∼Nσ))
        thesis₂ : (∃ λ γ → α ≡ B ⇒ γ) → Γ ⊢ P ∶ B → SN (M · P)
        thesis₂ α=β→γ P:B =
          let NP⇓ = proj₂ (SN-lemma  N⇓ (hi (B , n) (right (m<′n⊔m+1 {n} {m}))) N:α P⇓) α=β→γ P:B
          in exp (appl M→N) NP⇓ 

SN-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → SN M
SN-theo (⊢v _) = sne v
SN-theo (⊢· {α} {B} {M} M:α→β N:α) =
  let M⇓ = SN-theo M:α→β
  in proj₂ (SN-lemma M⇓ (wfₜ,ₙ< (α , height M⇓)) M:α→β (SN-theo N:α)) (B , refl) N:α
SN-theo (⊢ƛ M:α) = abs (SN-theo M:α) 

-- Main theorem

sn-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
sn-theo M:α = sound-SN (SN-theo M:α)
