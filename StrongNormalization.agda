module StrongNormalization where

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

data _ₜ<_ : Type → Type → Set where
  ₜ<l : ∀ {α β} → α ₜ< (α ⇒ β)
  ₜ<r : ∀ {α β} → β ₜ< (α ⇒ β)

wfₜ< : Well-founded _ₜ<_
wfₜ< τ = acc λ y ()
wfₜ< (A ⇒ B) = acc wfₜ<-aux
  where wfₜ<-aux : (γ : Type) → γ ₜ< (A ⇒ B) → Acc _ₜ<_ γ
        wfₜ<-aux .A ₜ<l = wfₜ< A
        wfₜ<-aux .B ₜ<r = wfₜ< B
        
open Transitive-closure _ₜ<_ renaming (_<⁺_ to _ₜ<⁺_)

wfₜ<⁺ : Well-founded _ₜ<⁺_ 
wfₜ<⁺ = well-founded wfₜ<

open Lexicographic _ₜ<⁺_ (λ _ m n → m <′ n) renaming (_<_ to _ₜ,ₙ<_ ; well-founded to wfΣ)

wfₜ,ₙ< : Well-founded _ₜ,ₙ<_
wfₜ,ₙ< = wfΣ wfₜ<⁺ <-well-founded

-- Definitions

data IsVar : Λ → Set where
  isv : ∀ {x} → IsVar (v x)

Unary : Σ → Λ → Set
Unary σ M = ∀ {x} → IsVar (σ x) ⊎ σ x ≡ M 

height→   : ∀ {M N} → M →SN N → ℕ 
heightNe  : ∀ {M x} → SNe x M → ℕ 
height    : ∀ {M} → SN M → ℕ 

height→ (αsn M→N N∼P) = suc (height→ M→N)
height→ (β N⇓) = suc (height N⇓)
height→ (appl M→N) = suc (height→ M→N)

heightNe v = 0
heightNe (app M⇓ N⇓) = suc (heightNe M⇓ ⊔ height N⇓)

height (abs M⇓) = suc (height M⇓)
height (sne M⇓) = suc (heightNe M⇓)
height (exp M→N N⇓) = suc (height→ M→N ⊔ height N⇓)

-- Auxiliary lemmas

--lemma< : ∀ {m n p} → m ≡ n → n <′ p → m <′ p
--lemma< refl n<p = n<p

--lemma≡suc : ∀ {m n} → m ≡ n → suc m ≡ suc n
--lemma≡suc refl = refl

--lemma≡⊔ : ∀ {m n p q} → m ≡ n → p ≡ q → m ⊔ p ≡ n ⊔ q
--lemma≡⊔ refl refl = refl

m<′m⊔n+1 : ∀ m n → m <′ suc (m ⊔ n)
m<′m⊔n+1 m n = s≤′s (≤⇒≤′ (m≤m⊔n m n))

⊔-comm = IsCommutativeMonoid.comm (IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid ⊔-⊓-0-isCommutativeSemiringWithoutOne)

m<′n⊔m+1 : ∀ m n → m <′ suc (n ⊔ m)
m<′n⊔m+1 m n with n ⊔ m | ⊔-comm n m
m<′n⊔m+1 m n | .(m ⊔ n) | refl = m<′m⊔n+1 m n

lemma-Unaryι : ∀ {x M} → Unary (ι ≺+ (x , M)) M
lemma-Unaryι {x} {_} {y} with x ≟ y 
... | yes _ = inj₂ refl
... | no _ = inj₁ isv

lemma-Unary≺+ : ∀ {x y M σ} → Unary σ M → Unary (σ ≺+ (x , v y)) M
lemma-Unary≺+ {x} {_} {_} {σ} unary {w} with x ≟ w
... | yes _ = inj₁ isv
... | no _ = unary {w}

SNe-preservedby-σ→SN : ∀ {σ x M N} → SNe x M → IsVar (σ x) → M ∙ σ →SN N → ⊥
SNe-preservedby-σ→SN = {!!}

SNe-preservedby-σ : ∀ {σ x M} → SNe x M → IsVar (σ x) → SN (M ∙ σ) → ∃ λ y → SNe y (M ∙ σ)
SNe-preservedby-σ {σ} {x} v isvarσx xσ⇓ with σ x
SNe-preservedby-σ {σ} {x} v (isv {.y}) (sne (v {.y})) | v y = y , v
SNe-preservedby-σ {σ} {x} v (isv {.y}) (exp y→M _) | v y = ⊥-elim (SNe-preservedby-σ→SN (v {x}) (isv {y}) y→M)
SNe-preservedby-σ {σ} {x} (app P⇓ Q⇓) _ (sne (app {y} Pσ⇓ Qσ⇓)) = y , app Pσ⇓ Qσ⇓ 
SNe-preservedby-σ {σ} {x} (app P⇓ Q⇓) isvarσx (exp PQσ→M _) = ⊥-elim (SNe-preservedby-σ→SN (app P⇓ Q⇓) isvarσx PQσ→M)

lemma-≡Γx : ∀ {α β Γ x} → Γ ⊢ v x ∶ α → Γ ⊢ v x ∶ β → α ≡ β
lemma-≡Γx (⊢v x∈Γ₁) (⊢v x∈Γ₂) = lemma∈!⟨⟩ x∈Γ₁ x∈Γ₂

lemma-ₜ≤ : ∀ {α β Γ M x} → SNe x M → Γ ⊢ v x ∶ β → Γ ⊢ M ∶ α → α ₜ<⁺ β ⊎ α ≡ β 
lemma-ₜ≤  v hdM:β hdM:α = inj₂ (lemma-≡Γx hdM:α hdM:β)
lemma-ₜ≤  {A} {B} (app M⇓ _) hdM:β (⊢· M:γ→α _) with lemma-ₜ≤ M⇓ hdM:β M:γ→α
... | inj₁ γ→α<β = inj₁ (trans [ ₜ<r ] γ→α<β)
lemma-ₜ≤ {A} .{γ ⇒ A} (app M⇓ _) hdM:β (⊢· {γ} M:γ→α _) | inj₂ refl = inj₁ [ ₜ<r ]

lemma-ₜ< : ∀ {α γ β Γ M x} → SNe x M → Γ ⊢ v x ∶ β → Γ ⊢ M ∶ α ⇒ γ → α ₜ<⁺ β
lemma-ₜ< M⇓ hdM:β M:α→γ with lemma-ₜ≤ M⇓ hdM:β M:α→γ 
... | inj₁ α→γ<β = trans [ ₜ<l ] α→γ<β
lemma-ₜ< {A} {γ} .{A ⇒ γ} M⇓ hdM:β M:α→γ | inj₂ refl = [ ₜ<l ]

→SN⊂→α : ∀ {M N} → M →SN N → M →α* N
→SN⊂→α (αsn M→N N∼P) = trans (→SN⊂→α M→N) (just (inj₂ N∼P))
→SN⊂→α (β _)  = just (inj₁ (ctxinj ▹β))
→SN⊂→α (appl M→M') = app-star-l (→SN⊂→α M→M')

lemmaσ⇂· : ∀ {σ Γ Δ P Q} → σ ∶ Γ ⇀ Δ ⇂ P · Q → (σ ∶ Γ ⇀ Δ ⇂ P) × (σ ∶ Γ ⇀ Δ ⇂ Q)
lemmaσ⇂· σ⇂PQ = (λ x*P → σ⇂PQ (*·l x*P)) , (λ x*Q → σ⇂PQ (*·r x*Q))

≡→α : ∀ {M N} -> M ≡ N -> M ∼α N
≡→α {M} M≡N = subst₂ _∼α_ refl M≡N (∼ρ {M})

-- Main lemma

SN-lemma : ∀ {M Γ α β N}
         → (M⇓ : SN M)
         → Acc _ₜ,ₙ<_ (β , height M⇓)
         → Γ ⊢ M ∶ α
         → SN N
         → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ N → Δ ⊢ N ∶ β → SN (M ∙ σ))
           × ((∃ λ γ → α ≡ β ⇒ γ) → Γ ⊢ N ∶ β → SN (M · N)) 

SN-lemma→ : ∀ {M N σ Γ Δ α β P}
          → (M→N : M →SN N)
          → Acc _ₜ,ₙ<_ (β , height→ M→N)
          → Γ ⊢ M ∶ α
          → σ ∶ Γ ⇀ Δ ⇂ M
          → Unary σ P
          → SN P
          → Δ ⊢ P ∶ β
          → ∃ λ Q → (M ∙ σ) →SN Q × Q ∼α N ∙ σ

SN-lemmaNe : ∀ {M Γ α β x N}
           → (M⇓ : SNe x M)
           → Acc _ₜ,ₙ<_ (β , heightNe M⇓)
           → Γ ⊢ M ∶ α
           → SN N
           → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ N → Δ ⊢ N ∶ β → SN (M ∙ σ))
             × ((∃ λ γ → α ≡ β ⇒ γ) → Γ ⊢ N ∶ β → SN (M · N)) 

SN-lemma→ {_} {_} {σ} {Γ} {Δ} {α} {B} (αsn M→N N∼P) (acc hi) M:A σ⇂M Πσ P⇓ P:B =
  let Q , Mσ→Q , Q∼Nσ = SN-lemma→ M→N (hi (B , height→ M→N) (right ≤′-refl)) M:A σ⇂M Πσ P⇓ P:B
      Nσ∼Pσ = ≡→α (lemmaM∼M'→Mσ≡M'σ N∼P)
  in Q , Mσ→Q , ∼τ Q∼Nσ Nσ∼Pσ
SN-lemma→ {ƛ x L · J} {_} {σ} {Γ} {Δ} {α} {B} (β J⇓) (acc hi) (⊢· _ J:γ) σ⇂ƛxLJ Πσ P⇓ P:B =
  let z : V
      z = χ (σ , ƛ x L)
      L[σ,x=z][z=Jσ]~L[x=J]σ : L [ σ ∣ x := v z ] [ z := J ∙ σ ] ∼α L [ x := J ] ∙ σ
      L[σ,x=z][z=Jσ]~L[x=J]σ = lemma∼α∙ (χ-lemma2 σ (ƛ x L))
      σ⇂J : σ ∶ Γ ⇀ Δ ⇂ J
      σ⇂J = proj₂ (lemmaσ⇂· σ⇂ƛxLJ)
      Jσ⇓ : SN (J ∙ σ)
      Jσ⇓ = proj₁ (SN-lemma J⇓ (hi (B , height J⇓) (right ≤′-refl)) J:γ P⇓) σ⇂J Πσ P:B
  in L [ σ ∣ x := v z ] [ z := J ∙ σ ] , β Jσ⇓ , L[σ,x=z][z=Jσ]~L[x=J]σ
SN-lemma→ {L · J} {L' · .J} {σ} {Γ} {Δ} {_} {B} (appl L→L') (acc hi) (⊢· L:γ _) σ⇂LJ Πσ P⇓ P:B =
  let σ⇂L : σ ∶ Γ ⇀ Δ ⇂ L
      σ⇂L = proj₁ (lemmaσ⇂· σ⇂LJ)
      P , Lσ→P , P~L'σ = SN-lemma→ L→L' (hi (B , height→ L→L') (right ≤′-refl)) L:γ σ⇂L Πσ P⇓ P:B
      PJσ~L'Jσ : P · (J ∙ σ) ∼α L' · J ∙ σ 
      PJσ~L'Jσ = ∼· P~L'σ ∼ρ
      LJσ→PJσ : L · J ∙ σ →SN P · (J ∙ σ)
      LJσ→PJσ = appl Lσ→P
  in P · (J ∙ σ) , LJσ→PJσ , PJσ~L'Jσ

SN-lemmaNe .{v x} {Γ} {_} {B} {.x} {N} (v {x}) _ _ N⇓  = thesis₁ , λ _ _ → sne (app v N⇓)
  where thesis₁ : ∀ {σ} {Δ} → σ ∶ Γ ⇀ Δ ⇂ (v x) → Unary σ N → Δ ⊢ N ∶ B → SN (v x ∙ σ)
        thesis₁ {σ} _ unary _ with σ x | unary {x} 
        ... | .(v y) | inj₁ (isv {y}) = sne v
        ... | _ | inj₂ refl = N⇓ 
SN-lemmaNe {P · Q} {Γ} {_} {B} {.x} {N} (app {x} P⇓ Q⇓) (acc hi) (⊢· {γ} {ε} P:γ→ε Q:γ) N⇓ =
  thesis₁ , λ _ _ → sne (app (app P⇓ Q⇓) N⇓)
    where
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ P · Q → Unary σ N → Δ ⊢ N ∶ B → SN (P · Q ∙ σ)
        thesis₁ {σ} {Δ} σ⇂PQ unary N:B =
          let m , n = heightNe P⇓ , height Q⇓
              σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
              σ⇂P = λ x*P → σ⇂PQ (*·l x*P)
              Pσ⇓ : SN (P ∙ σ)
              Pσ⇓ = proj₁ (SN-lemmaNe P⇓ (hi (B , m) (right (m<′m⊔n+1 m n))) P:γ→ε N⇓) σ⇂P unary N:B
              σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
              σ⇂Q = λ x*Q → σ⇂PQ (*·r x*Q)
              Qσ⇓ : SN (Q ∙ σ)
              Qσ⇓ = proj₁ (SN-lemma Q⇓ (hi (B , n) (right (m<′n⊔m+1 n m))) Q:γ N⇓) σ⇂Q unary N:B
              Pσ:γ→ε : Δ ⊢ P ∙ σ ∶ γ ⇒ ε
              Pσ:γ→ε = lemma⊢σM P:γ→ε σ⇂P                                                                            
              Qσ:γ : Δ ⊢ Q ∙ σ ∶ γ 
              Qσ:γ = lemma⊢σM Q:γ σ⇂Q
              PQσ⇓₁ = λ isvσx → sne (app (proj₂ (SNe-preservedby-σ {σ} {x} {P} P⇓ isvσx Pσ⇓)) Qσ⇓)
              PQσ⇓₂ = λ { σx≡N →
                let γ<β : γ ₜ<⁺ B
                    γ<β = {!!} --lemma-ₜ< P⇓ hdP:β P:γ→ε
                in proj₂ (SN-lemma Pσ⇓ (hi (γ , height Pσ⇓) (left γ<β)) Pσ:γ→ε Qσ⇓) (ε , refl) Qσ:γ }
          in [ PQσ⇓₁ , PQσ⇓₂ ]′ (unary {x})
                                  
SN-lemma {β = B} (sne M⇓) (acc hi) = SN-lemmaNe M⇓ (hi (B , heightNe M⇓) (right ≤′-refl))
SN-lemma {ƛ x P} {Γ} {δ ⇒ ε} {B} {N} (abs P⇓) (acc hi) (⊢ƛ P:ε) N⇓ = thesis₁ , thesis₂ (⊢ƛ P:ε)
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ ƛ x P → Unary σ N → Δ ⊢ N ∶ B → SN (ƛ x P ∙ σ)
        thesis₁ {σ} {Δ} σ⇂ƛxP Πσ N:B =
          let z : V
              z = χ (σ , ƛ x P)
              σ⇂P : (σ ≺+ (x , v z)) ∶ (Γ ‚ x ∶ δ) ⇀ (Δ ‚ z ∶ δ)  ⇂ P
              σ⇂P = lemmaaux⇀ (χ-lemma2 σ (ƛ x P)) σ⇂ƛxP
              Πσ,x=z : Unary (σ ≺+ (x , v z)) N
              Πσ,x=z = lemma-Unary≺+ {x} {z} Πσ
              Δ,z:δ⊢N:B : Δ ‚ z ∶ δ ⊢ N ∶ B
              Δ,z:δ⊢N:B = {!!}
              Pσ,x=z⇓ = proj₁ (SN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:ε N⇓) σ⇂P Πσ,x=z Δ,z:δ⊢N:B
          in abs Pσ,x=z⇓
        thesis₂ : ∀ {δ ε} → Γ ⊢ ƛ x P ∶ δ ⇒ ε → (∃ λ γ → δ ⇒ ε ≡ B ⇒ γ) → Γ ⊢ N ∶ B → SN (ƛ x P · N)
        thesis₂ {.B} {.γ} (⊢ƛ P:γ) (γ , refl) N:B =
          let x=N⇂P : (ι ≺+ (x , N)) ∶ (Γ ‚ x ∶ B) ⇀ Γ ⇂ P
              x=N⇂P = lemma⇀ (lemmaι≺+⇀ N:B)
              Πx=N : Unary (ι ≺+ (x , N)) N
              Πx=N = lemma-Unaryι {x} {N}
              Px=N⇓ = proj₁ (SN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:γ N⇓) x=N⇂P Πx=N N:B
          in exp (β N⇓) Px=N⇓
SN-lemma {M} {Γ} {α} {B} {P} (exp {.M} {N} M→N N⇓) (acc hi) M:α P⇓ = thesis₁ , thesis₂
  where m = height→ M→N
        n = height N⇓ 
        M→αN : M →α* N
        M→αN = →SN⊂→α M→N
        N:α : Γ ⊢ N ∶ α
        N:α = lemma⊢→α* M:α M→αN
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ P → Δ ⊢ P ∶ B → SN (M ∙ σ)
        thesis₁ {σ} {Δ} σ⇂M Πσ P:B =
          let _ , Mσ→P , P∼Nσ = SN-lemma→ M→N (hi (B , m) (right (m<′m⊔n+1 m n))) M:α σ⇂M Πσ P⇓ P:B
              σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
              σ⇂N = λ x*N → σ⇂M ((dual-#-* lemma→α*#) x*N M→αN)
              Nσ⇓ : SN (N ∙ σ)
              Nσ⇓ = proj₁ (SN-lemma N⇓ (hi (B , n) (right (m<′n⊔m+1 n m))) N:α P⇓) σ⇂N Πσ P:B
          in exp (αsn Mσ→P P∼Nσ) Nσ⇓
        thesis₂ : (∃ λ γ → α ≡ B ⇒ γ) → Γ ⊢ P ∶ B → SN (M · P)
        thesis₂ α=β→γ P:B =
          let NP⇓ = proj₂ (SN-lemma  N⇓ (hi (B , n) (right (m<′n⊔m+1 n m))) N:α P⇓) α=β→γ P:B
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
