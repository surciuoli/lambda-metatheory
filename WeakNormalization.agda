module WeakNormalization where

open import Term
open import Chi
open import Substitution
open import Data.Sum
open import Data.Product hiding (Σ)
open import Beta
open import Alpha
open import SubstitutionLemmas
open import ListProperties
open import Relation using (just; trans) renaming (refl to reflR)
open import Unary
open import TypeLemmas
open import ParallelReduction
open import SubstitutionCompatibilityLemmas hiding (_↠_)
open import Neutral

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

-- Definitions

data WN : Λ → Set
data WNe : V → Λ → Set 

data WNe where
  var : ∀ {x} → WNe x (v x)
  app : ∀ {x M N} → WNe x M → WN N → WNe x (M · N)

data WN where
  wke : ∀ {M x} → WNe x M → WN M 
  abs : ∀ {x M} → WN M → WN (ƛ x M) 
  exp : ∀ {M N} → M ↠ N → WN N → WN M

heightNe : ∀ {M x} → WNe x M → ℕ 
height   : ∀ {M} → WN M → ℕ 

heightNe var = 0
heightNe (app M⇓ N⇓) = suc (heightNe M⇓ ⊔ height N⇓)

height (abs M⇓) = suc (height M⇓)
height (wke M⇓) = suc (heightNe M⇓)
height (exp _ M⇓) = suc (height M⇓)
  
-- Auxiliary lemmas

m<′m⊔n+1 : ∀ m n → m <′ suc (m ⊔ n)
m<′m⊔n+1 m n = s≤′s (≤⇒≤′ (m≤m⊔n m n))

⊔-comm = IsCommutativeMonoid.comm (IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid ⊔-⊓-0-isCommutativeSemiringWithoutOne)

m<′n⊔m+1 : ∀ m n → m <′ suc (n ⊔ m)
m<′n⊔m+1 m n with n ⊔ m | ⊔-comm n m
m<′n⊔m+1 m n | .(m ⊔ n) | refl = m<′m⊔n+1 m n

lemmaσ⇂· : ∀ {σ Γ Δ P Q} → σ ∶ Γ ⇀ Δ ⇂ P · Q → (σ ∶ Γ ⇀ Δ ⇂ P) × (σ ∶ Γ ⇀ Δ ⇂ Q)
lemmaσ⇂· σ⇂PQ = (λ x*P → σ⇂PQ (*·l x*P)) , (λ x*Q → σ⇂PQ (*·r x*Q))

WNe⇒wne : ∀ {x M} → WNe x M → wne x M
WNe⇒wne var = var
WNe⇒wne (app M⇓ _) = app (WNe⇒wne M⇓)

ne⇒WNe : ∀ {x M} → ne x M → WNe x M
nf⇒WN : ∀ {M} → nf M → WN M

ne⇒WNe var = var
ne⇒WNe (app neM nfN) = app (ne⇒WNe neM) (nf⇒WN nfN)

nf⇒WN (nfe neM) = wke (ne⇒WNe neM)
nf⇒WN (abs nfM) = abs (nf⇒WN nfM)

-- Soundness WN
  
wn : Λ → Set
wn M = ∃ λ N → M ↠ N × nf N

sound-WN : ∀ {M} → WN M → wn M
sound-WNe : ∀ {x M} → WNe x M → wn M

sound-WN (wke M⇓) = sound-WNe M⇓
sound-WN (abs {x} M⇓) =
  let N , M→N , nfN = sound-WN M⇓
  in ƛ x N , abs-star M→N , abs nfN
sound-WN (exp M→N N⇓) =
  let P , N→P , nfP = sound-WN N⇓
  in P , trans M→N N→P , nfP

sound-WNe (var {x}) = v x , reflR , nfe var
sound-WNe (app M⇓ N⇓) =
  let M' , M→M' , nfM' = sound-WNe M⇓
      N' , N→N' , nfN' = sound-WN N⇓
      wneM' = lemma₁ (WNe⇒wne M⇓) M→M'
      neM' = corollary₁ wneM' nfM'
  in M' · N' , trans (app-star-l M→M') (app-star-r N→N') , nfe (app neM' nfN')

-- Main lemma

WN-lemma : ∀ {M Γ α β N}
         → (M⇓ : WN M)
         → Acc _ₜ,ₙ<_ (β , height M⇓)
         → Γ ⊢ M ∶ α
         → WN N
         → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ N Γ β → WN (M ∙ σ))
           × ((∃ λ γ → α ≡ β ⟶ γ) → Γ ⊢ N ∶ β → WN (M · N)) 

WN-lemmaNe : ∀ {M Γ α β x N}
           → (M⇓ : WNe x M)
           → Acc _ₜ,ₙ<_ (β , heightNe M⇓)
           → Γ ⊢ M ∶ α
           → WN N
           → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ N Γ β → WN (M ∙ σ))
             × ((∃ λ γ → α ≡ β ⟶ γ) → Γ ⊢ N ∶ β → WN (M · N)) 

WN-lemmaNe .{v x} {Γ} {_} {B} {.x} {N} (var {x}) _ _ N⇓  = thesis₁ , λ _ _ → wke (app var N⇓)
  where thesis₁ : ∀ {σ} {Δ} → σ ∶ Γ ⇀ Δ ⇂ (v x) → Unary σ N Γ B → WN (v x ∙ σ)
        thesis₁ {σ} _ Unyσ with σ x | Unyσ {x} 
        ... | .(v y) | inj₁ (isv {y}) = wke var
        ... | _ | inj₂ (refl , _) = N⇓ 
WN-lemmaNe {P · Q} {Γ} {_} {B} {.x} {N} (app {x} P⇓ Q⇓) (acc hi) (⊢· {γ} {ε} P:γ→ε Q:γ) N⇓ =
  thesis₁ , λ _ _ → wke (app (app P⇓ Q⇓) N⇓)
    where
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ P · Q → Unary σ N Γ B → WN (P · Q ∙ σ)
        thesis₁ {σ} {Δ} σ⇂PQ Unyσ =
          let m , n = heightNe P⇓ , height Q⇓
              σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
              σ⇂P = λ x*P → σ⇂PQ (*·l x*P)
              Pσ⇓ : WN (P ∙ σ)
              Pσ⇓ = proj₁ (WN-lemmaNe P⇓ (hi (B , m) (right (m<′m⊔n+1 m n))) P:γ→ε N⇓) σ⇂P Unyσ
              σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
              σ⇂Q = λ x*Q → σ⇂PQ (*·r x*Q)
              Qσ⇓ : WN (Q ∙ σ)
              Qσ⇓ = proj₁ (WN-lemma Q⇓ (hi (B , n) (right (m<′n⊔m+1 n m))) Q:γ N⇓) σ⇂Q Unyσ
              Pσ:γ→ε : Δ ⊢ P ∙ σ ∶ γ ⟶ ε
              Pσ:γ→ε = lemma⊢σM P:γ→ε σ⇂P                                                                            
              Qσ:γ : Δ ⊢ Q ∙ σ ∶ γ 
              Qσ:γ = lemma⊢σM Q:γ σ⇂Q
              PQσ⇓₁ = λ IsVarσx →
                let R , Pσ→R , nfR = sound-WN Pσ⇓
                    y , σx≡y = IsVar⇒∃y σ x IsVarσx
                    wneP = WNe⇒wne P⇓
                    wnePσ = lemma₃ wneP σx≡y
                    wneR = lemma₁ wnePσ Pσ→R 
                    neR = corollary₁ wneR nfR
                    R⇓ = ne⇒WNe neR
                 in exp (app-star-l Pσ→R) (wke (app R⇓ Qσ⇓))
              PQσ⇓₂ = λ { (_ , Γ⊢x:B) →
                let γ<β : γ ₜ<⁺ B
                    γ<β = lemma-ₜ< (WNe⇒wne P⇓) Γ⊢x:B P:γ→ε
                in proj₂ (WN-lemma Pσ⇓ (hi (γ , height Pσ⇓) (left γ<β)) Pσ:γ→ε Qσ⇓) (ε , refl) Qσ:γ }
          in [ PQσ⇓₁ , PQσ⇓₂ ]′ (Unyσ {x})
                                  
WN-lemma {β = B} (wke M⇓) (acc hi) = WN-lemmaNe M⇓ (hi (B , heightNe M⇓) (right ≤′-refl))
WN-lemma {ƛ x P} {Γ} {δ ⟶ ε} {B} {N} (abs P⇓) (acc hi) (⊢ƛ P:ε) N⇓ = thesis₁ , thesis₂ (⊢ƛ P:ε)
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ ƛ x P → Unary σ N Γ B → WN (ƛ x P ∙ σ)
        thesis₁ {σ} {Δ} σ⇂ƛxP Unyσ =
          let z : V
              z = χ (σ , ƛ x P)
              σ⇂P : (σ ≺+ (x , v z)) ∶ (Γ ‚ x ∶ δ) ⇀ (Δ ‚ z ∶ δ) ⇂ P
              σ⇂P = lemmaaux⇀ (χ-lemma2 σ (ƛ x P)) σ⇂ƛxP
              Unyσ,x=z : Unary (σ ≺+ (x , v z)) N (Γ ‚ x ∶ δ) B
              Unyσ,x=z = lemma-Unary≺+ Unyσ
              Pσ,x=z⇓ = proj₁ (WN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:ε N⇓) σ⇂P Unyσ,x=z
          in abs Pσ,x=z⇓
        thesis₂ : ∀ {δ ε} → Γ ⊢ ƛ x P ∶ δ ⟶ ε → (∃ λ γ → δ ⟶ ε ≡ B ⟶ γ) → Γ ⊢ N ∶ B → WN (ƛ x P · N)
        thesis₂ {.B} {.γ} (⊢ƛ P:γ) (γ , refl) N:B =
          let x=N⇂P : (ι ≺+ (x , N)) ∶ (Γ ‚ x ∶ B) ⇀ Γ ⇂ P
              x=N⇂P = lemma⇀ (lemmaι≺+⇀ N:B)
              Unyx=N : Unary (ι ≺+ (x , N)) N (Γ ‚ x ∶ B) B
              Unyx=N = lemma-Unaryι N:B
              Px=N⇓ = proj₁ (WN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:γ N⇓) x=N⇂P Unyx=N
          in exp (just (inj₁ (ctxinj ▹β))) Px=N⇓
WN-lemma {M} {Γ} {α} {B} {P} (exp {.M} {N} M↠N N⇓) (acc hi) M:α P⇓ = thesis₁ , thesis₂
  where n = height N⇓ 
        N:α : Γ ⊢ N ∶ α
        N:α = lemma⊢→α* M:α M↠N
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ P Γ B → WN (M ∙ σ)
        thesis₁ {σ} {Δ} σ⇂M Unyσ =
          let σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
              σ⇂N = λ x*N → σ⇂M ((dual-#-* lemma→α*#) x*N M↠N)
              Nσ⇓ : WN (N ∙ σ)
              Nσ⇓ = proj₁ (WN-lemma N⇓ (hi (B , n) (right ≤′-refl)) N:α P⇓) σ⇂N Unyσ
          in exp (subst-compat↠ M↠N) Nσ⇓
        thesis₂ : (∃ λ γ → α ≡ B ⟶ γ) → Γ ⊢ P ∶ B → WN (M · P)
        thesis₂ α=β→γ P:B =
          let NP⇓ = proj₂ (WN-lemma  N⇓ (hi (B , n) (right ≤′-refl)) N:α P⇓) α=β→γ P:B
          in exp (app-star-l M↠N) NP⇓ 

WN-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → WN M
WN-theo (⊢v _) = wke var
WN-theo (⊢· {α} {B} {M} M:α→β N:α) =
  let M⇓ = WN-theo M:α→β
  in proj₂ (WN-lemma M⇓ (wfₜ,ₙ< (α , height M⇓)) M:α→β (WN-theo N:α)) (B , refl) N:α
WN-theo (⊢ƛ M:α) = abs (WN-theo M:α) 

-- Main theorem

wn-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → wn M
wn-theo M:α = sound-WN (WN-theo M:α)
