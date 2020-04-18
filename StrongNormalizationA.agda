module StrongNormalizationA where

open import SoundnessSN
open import Term 
open import Chi
open import Substitution
open import Data.Sum
open import Data.Product hiding (Σ)
open import Beta
open import Alpha
open import SubstitutionLemmas
open import ListProperties
open import Relation using (just; trans)
open import Unary
open import TypeLemmas
open import SubstitutionCompatibilityLemmas

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

height→  : ∀ {M N} → M →SN N → ℕ 
heightNe : ∀ {M x} → SNe x M → ℕ 
height   : ∀ {M} → SN M → ℕ 

height→ (β N⇓) = suc (height N⇓)
height→ (appl M→N) = suc (height→ M→N)
height→ (αsn M→N N∼P) = suc (height→ M→N)

heightNe v = 0
heightNe (app M⇓ N⇓) = suc (heightNe M⇓ ⊔ height N⇓)

height (abs M⇓) = suc (height M⇓)
height (sne M⇓) = suc (heightNe M⇓)
height (exp M→N N⇓) = suc (height→ M→N ⊔ height N⇓)

-- Auxiliary lemmas

m<′m⊔n+1 : ∀ m n → m <′ suc (m ⊔ n)
m<′m⊔n+1 m n = s≤′s (≤⇒≤′ (m≤m⊔n m n))

⊔-comm = IsCommutativeMonoid.comm (IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid ⊔-⊓-0-isCommutativeSemiringWithoutOne)

m<′n⊔m+1 : ∀ m n → m <′ suc (n ⊔ m)
m<′n⊔m+1 m n with n ⊔ m | ⊔-comm n m
m<′n⊔m+1 m n | .(m ⊔ n) | refl = m<′m⊔n+1 m n

→SN⊂→α : ∀ {M N} → M →SN N → M →α* N
→SN⊂→α (β _)  = just (inj₁ (ctxinj ▹β))
→SN⊂→α (appl M→M') = app-star-l (→SN⊂→α M→M')
→SN⊂→α (αsn M→N N∼P) = trans (→SN⊂→α M→N) (just (inj₂ N∼P))

lemmaσ⇂· : ∀ {σ Γ Δ P Q} → σ ∶ Γ ⇀ Δ ⇂ P · Q → (σ ∶ Γ ⇀ Δ ⇂ P) × (σ ∶ Γ ⇀ Δ ⇂ Q)
lemmaσ⇂· σ⇂PQ = (λ x*P → σ⇂PQ (*·l x*P)) , (λ x*Q → σ⇂PQ (*·r x*Q))

≡⇒α : ∀ {M N} → M ≡ N → M ∼α N
≡⇒α {M} M≡N = subst₂ _∼α_ refl M≡N (∼ρ {M})

invol≺+ : ∀ {σ x M P} → x # P → (σ ≺+ (x , M)) ≅ σ ⇂ P
invol≺+ {σ} {x} {M} {P} x#P = ∼*ρ , aux
  where aux : (y : V) → y * P → (σ ≺+ (x , M)) y ≡ σ y
        aux y y*P with x ≟ y
        ... | no _ = refl
        aux .x x*P | yes refl = ⊥-elim (lemma-free→¬# x*P x#P)

weaken-dom : ∀ {x M σ Γ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → σ ∶ Γ ⇀ Δ ⇂ ƛ x M
weaken-dom {x} {M} {σ} {Γ} {Δ} σ⇂M = λ y*M → aux y*M
  where aux : ∀ {x y} → y * ƛ x M → (p : y ∈ Γ) → Δ ⊢ σ y ∶ Γ ⟨ p ⟩
        aux {x} {y} (*ƛ x*M _) y∈Γ with y ≟ x
        ... | no _ = σ⇂M x*M y∈Γ
        aux {x} {.x} (*ƛ _ x≢x) _ | yes refl = ⊥-elim (x≢x refl)

-- Main lemma

SN-lemma : ∀ {M Γ α β N}
         → (M⇓ : SN M)
         → Acc _ₜ,ₙ<_ (β , height M⇓)
         → Γ ⊢ M ∶ α
         → SN N
         → (∀ {x σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ x N → Γ ⊢ v x ∶ β → SN (M ∙ σ))
           × ((∃ λ γ → α ≡ β ⟶ γ) → Γ ⊢ N ∶ β → SN (M · N)) 

SN-lemma→ : ∀ {M N σ Γ Δ α β P x}
          → (M→N : M →SN N)
          → Acc _ₜ,ₙ<_ (β , height→ M→N)
          → Γ ⊢ M ∶ α
          → SN P            
          → σ ∶ Γ ⇀ Δ ⇂ M        
          → Unary σ x P
          → Γ ⊢ v x ∶ β
          → (M ∙ σ) →SN (N ∙ σ)

SN-lemmaNe : ∀ {M Γ α β y N}
           → (M⇓ : SNe y M)
           → Acc _ₜ,ₙ<_ (β , heightNe M⇓)
           → Γ ⊢ M ∶ α
           → SN N
           → (∀ {x σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ x N → Γ ⊢ v x ∶ β → SN (M ∙ σ) × (y ≢ x → ∃ λ z → SNe z (M ∙ σ)))
             × ((∃ λ γ → α ≡ β ⟶ γ) → Γ ⊢ N ∶ β → SN (M · N)) 

SN-lemma→ {_} {_} {σ} {Γ} {Δ} {α} {B} (αsn M→N N∼P) (acc hi) M:A P⇓ σ⇂M Unyσ x:B =
  let Mσ→Nσ = SN-lemma→ M→N (hi (B , height→ M→N) (right ≤′-refl)) M:A P⇓ σ⇂M Unyσ x:B
      Nσ∼Pσ = ≡⇒α (lemmaM∼M'→Mσ≡M'σ N∼P)
  in αsn Mσ→Nσ Nσ∼Pσ
SN-lemma→ {ƛ y M · N} {_} {σ} {Γ} {Δ} {α} {B} {_} {x} (β N⇓) (acc hi) (⊢· _ N:γ) P⇓ σ⇂ƛyMN Unyσ x:B =
  let z : V
      z = χ (σ , ƛ y M)
      σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
      σ⇂N = proj₂ (lemmaσ⇂· σ⇂ƛyMN)
      Nσ⇓ : SN (N ∙ σ)
      Nσ⇓ = proj₁ (SN-lemma N⇓ (hi (B , height N⇓) (right ≤′-refl)) N:γ P⇓) σ⇂N Unyσ x:B
      Mσ,x=z,z=Nσ~Mx=Nσ : (M ∙ σ ≺+ (y , v z)) ∙ ι ≺+ (z , N ∙ σ) ∼α (M ∙ ι ≺+ (y , N)) ∙ σ
      Mσ,x=z,z=Nσ~Mx=Nσ = lemma∼α∙ (χ-lemma2 σ (ƛ y M))
  in αsn (β Nσ⇓) Mσ,x=z,z=Nσ~Mx=Nσ
SN-lemma→ {L · J} {L' · .J} {σ} {Γ} {Δ} {_} {B} (appl L→L') (acc hi) (⊢· L:γ _) P⇓ σ⇂LJ Unyσ x:B =
  let σ⇂L : σ ∶ Γ ⇀ Δ ⇂ L
      σ⇂L = proj₁ (lemmaσ⇂· σ⇂LJ)
      Lσ→L'σ = SN-lemma→ L→L' (hi (B , height→ L→L') (right ≤′-refl)) L:γ P⇓ σ⇂L Unyσ x:B
  in appl Lσ→L'σ

SN-lemmaNe .{v y} {Γ} {_} {B} {.y} {N} (v {y}) _ _ N⇓  = thesis₁ , λ _ _ → sne (app v N⇓)
  where thesis₁ : ∀ {x σ Δ} → σ ∶ Γ ⇀ Δ ⇂ (v y) → Unary σ x N → Γ ⊢ v x ∶ B → SN (v y ∙ σ) × (y ≢ x → ∃ λ z → SNe z (v y ∙ σ))
        thesis₁ {x} {σ} _ Unyσ _ with y ≟ x
        ... | no y≢x with σ y | (proj₂ Unyσ) y≢x
        ... | .(v z) | isv {z} = sne v , λ _ → z , v
        thesis₁ {.y} {σ} _ Unyσ _ | yes refl with σ y | proj₁ Unyσ
        ... | .N | refl = N⇓ , λ y≢x → ⊥-elim (y≢x refl)
SN-lemmaNe {P · Q} {Γ} {_} {B} {.y} {N} (app {y} P⇓ Q⇓) (acc hi) (⊢· {γ} {ε} P:γ→ε Q:γ) N⇓ = 
  thesis₁ , λ _ _ → sne (app (app P⇓ Q⇓) N⇓)
    where
        thesis₁ : ∀ {x σ Δ} → σ ∶ Γ ⇀ Δ ⇂ P · Q → Unary σ x N → Γ ⊢ v x ∶ B → SN (P · Q ∙ σ) × (y ≢ x → ∃ λ z → SNe z (P · Q ∙ σ))
        thesis₁ {x} {σ} {Δ} σ⇂PQ Unyσ x:B with y ≟ x
        ... | no y≢x =
          let m , n = heightNe P⇓ , height Q⇓
              σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
              σ⇂P = λ y*P → σ⇂PQ (*·l y*P)
              Pσ⇓ : ∃ λ z → SNe z (P ∙ σ)
              Pσ⇓ = proj₂ (proj₁ (SN-lemmaNe P⇓ (hi (B , m) (right (m<′m⊔n+1 m n))) P:γ→ε N⇓) σ⇂P Unyσ x:B) y≢x
              σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
              σ⇂Q = λ y*Q → σ⇂PQ (*·r y*Q)
              Qσ⇓ : SN (Q ∙ σ)
              Qσ⇓ = proj₁ (SN-lemma Q⇓ (hi (B , n) (right (m<′n⊔m+1 n m))) Q:γ N⇓) σ⇂Q Unyσ x:B
              PQσ⇓y = app (proj₂ Pσ⇓) Qσ⇓
          in sne PQσ⇓y , λ _ → (proj₁ Pσ⇓ , PQσ⇓y)
        thesis₁ {.y} {σ} {Δ} σ⇂PQ Unyσ y:B | yes refl =
          let m , n = heightNe P⇓ , height Q⇓
              σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
              σ⇂P = λ y*P → σ⇂PQ (*·l y*P)
              Pσ⇓ : SN (P ∙ σ)
              Pσ⇓ = proj₁ (proj₁ (SN-lemmaNe P⇓ (hi (B , m) (right (m<′m⊔n+1 m n))) P:γ→ε N⇓) σ⇂P Unyσ y:B)
              σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
              σ⇂Q = λ y*Q → σ⇂PQ (*·r y*Q)
              Qσ⇓ : SN (Q ∙ σ)
              Qσ⇓ = proj₁ (SN-lemma Q⇓ (hi (B , n) (right (m<′n⊔m+1 n m))) Q:γ N⇓) σ⇂Q Unyσ y:B
              Pσ:γ→ε : Δ ⊢ P ∙ σ ∶ γ ⟶ ε
              Pσ:γ→ε = lemma⊢σM P:γ→ε σ⇂P                                                                            
              Qσ:γ : Δ ⊢ Q ∙ σ ∶ γ 
              Qσ:γ = lemma⊢σM Q:γ σ⇂Q
              γ<β : γ ₜ<⁺ B
              γ<β = lemma-ₜ< (lemma-ne P⇓) y:B P:γ→ε
          in proj₂ (SN-lemma Pσ⇓ (hi (γ , height Pσ⇓) (left γ<β)) Pσ:γ→ε Qσ⇓) (ε , refl) Qσ:γ , λ y≢x → ⊥-elim (y≢x refl)
                                  
SN-lemma {β = B} (sne M⇓) (acc hi) M:α N⇓ =
  let th₁ , th₂ = SN-lemmaNe M⇓ (hi (B , heightNe M⇓) (right ≤′-refl)) M:α N⇓
  in (λ p1 p2 p3 → proj₁ (th₁ p1 p2 p3)) , th₂ 
SN-lemma {ƛ y P} {Γ} {δ ⟶ ε} {B} {N} (abs P⇓) (acc hi) (⊢ƛ P:ε) N⇓ = thesis₁ , thesis₂ P:ε
  where thesis₁ : ∀ {x σ Δ} → σ ∶ Γ ⇀ Δ ⇂ ƛ y P → Unary σ x N → Γ ⊢ v x ∶ B → SN (ƛ y P ∙ σ)
        thesis₁ {x} {σ} {Δ} σ⇂ƛyP Unyσ x:B with y ≟ x
        ... | no y≢x =
          let z : V
              z = χ (σ , ƛ y P)
              σ,y=z⇂P : (σ ≺+ (y , v z)) ∶ (Γ ‚ y ∶ δ) ⇀ (Δ ‚ z ∶ δ) ⇂ P
              σ,y=z⇂P = lemmaaux⇀ (χ-lemma2 σ (ƛ y P)) σ⇂ƛyP
              Unyσ,y=z : Unary (σ ≺+ (y , v z)) x N
              Unyσ,y=z = unary≺+≢ y≢x Unyσ
              x:B' : Γ ‚ y ∶ δ ⊢ v x ∶ B 
              x:B' = lemmaWeakening⊢# (#v (sym≢ y≢x)) x:B
              Pσ,y=z⇓ : SN (P ∙ (σ ≺+ (y , v z)))
              Pσ,y=z⇓ = proj₁ (SN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:ε N⇓) σ,y=z⇂P Unyσ,y=z x:B'
          in abs Pσ,y=z⇓
        thesis₁ {.y} {σ} {Δ} σ⇂ƛyP Unyσ y:B | yes refl =
          let z : V
              z = χ (σ , ƛ y P)
              u : V
              u = χ (ι , P)      
              w : V
              w = χ (σ ≺+ (y , v z) , ƛ u P)
              σ,y=z⇂P : (σ ≺+ (y , v z)) ∶ (Γ ‚ y ∶ δ) ⇀ (Δ ‚ z ∶ δ) ⇂ P
              σ,y=z⇂P = lemmaaux⇀ (χ-lemma2 σ (ƛ y P)) σ⇂ƛyP
              σ,y=z⇂ƛuP : (σ ≺+ (y , v z)) ∶ (Γ ‚ y ∶ δ) ⇀ (Δ ‚ z ∶ δ) ⇂ ƛ u P
              σ,y=z⇂ƛuP = weaken-dom σ,y=z⇂P
              σ⇂P : (σ ≺+ (y , v z) ≺+ (u , v w)) ∶ (Γ ‚ y ∶ δ ‚ u ∶ B) ⇀ (Δ ‚ z ∶ δ ‚ w ∶ B) ⇂ P
              σ⇂P = lemmaaux⇀ (χ-lemma2 (σ ≺+ (y , v z)) (ƛ u P)) σ,y=z⇂ƛuP
              Unyσ,y=z,u=w : Unary (σ ≺+ (y , v z) ≺+ (u , v w)) u (v w)
              Unyσ,y=z,u=w = unaryv (unary≺+≡ Unyσ)
              u:B : Γ ‚ y ∶ δ ‚ u ∶ B ⊢ v u ∶ B
              u:B = ⊢v (here refl)
              u#P : u # P
              u#P = lemmaM∼N# (∼σ lemma∙ι) u (lemmafree#→# (χ-lemma2 ι P))
              P:ε' : Γ ‚ y ∶ δ ‚ u ∶ B ⊢ P ∶ ε
              P:ε' = lemmaWeakening⊢# u#P P:ε
              Pσ,y=z,u=w⇓ : SN (P ∙ (σ ≺+ (y , v z) ≺+ (u , v w)))
              Pσ,y=z,u=w⇓ = proj₁ (SN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:ε' (sne v)) σ⇂P Unyσ,y=z,u=w u:B
              σ,y=z,u=w≡σ,y=z : (σ ≺+ (y , v z) ≺+ (u , v w)) ≅ σ ≺+ (y , v z) ⇂ P
              σ,y=z,u=w≡σ,y=z = invol≺+ u#P
              Pσ,y=z⇓ : SN (P ∙ (σ ≺+ (y , v z)))
              Pσ,y=z⇓ = subst SN (lemma-subst-σ≡ σ,y=z,u=w≡σ,y=z) Pσ,y=z,u=w⇓
          in abs Pσ,y=z⇓
        thesis₂ : ∀ {δ ε} → Γ ‚ y ∶ δ ⊢ P ∶ ε → (∃ λ γ → δ ⟶ ε ≡ B ⟶ γ) → Γ ⊢ N ∶ B → SN (ƛ y P · N)
        thesis₂ {.B} {.γ} P:γ (γ , refl) N:B =
          let y=N⇂P : (ι ≺+ (y , N)) ∶ (Γ ‚ y ∶ B) ⇀ Γ ⇂ P
              y=N⇂P = lemma⇀ (lemmaι≺+⇀ N:B)
              Unyy=N : Unary (ι ≺+ (y , N)) y N
              Unyy=N = unary
              Γ,y:B⊢y:B : Γ ‚ y ∶ B ⊢ v y ∶ B
              Γ,y:B⊢y:B = ⊢v (here refl)
              Py=N⇓ = proj₁ (SN-lemma P⇓ (hi (B , height P⇓) (right ≤′-refl)) P:γ N⇓) y=N⇂P Unyy=N Γ,y:B⊢y:B
          in exp (β N⇓) Py=N⇓
SN-lemma {M} {Γ} {α} {B} {P} (exp {.M} {N} M→N N⇓) (acc hi) M:α P⇓ = thesis₁ , thesis₂
  where m = height→ M→N
        n = height N⇓ 
        M→αN : M →α* N
        M→αN = →SN⊂→α M→N
        N:α : Γ ⊢ N ∶ α
        N:α = lemma⊢→α* M:α M→αN
        thesis₁ : ∀ {x σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ x P → Γ ⊢ v x ∶ B → SN (M ∙ σ)
        thesis₁ {x} {σ} {Δ} σ⇂M Unyσ x:B =
          let Mσ→Nσ = SN-lemma→ M→N (hi (B , m) (right (m<′m⊔n+1 m n))) M:α P⇓ σ⇂M Unyσ x:B
              σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
              σ⇂N = λ y*N → σ⇂M ((dual-#-* lemma→α*#) y*N M→αN)
              Nσ⇓ : SN (N ∙ σ)
              Nσ⇓ = proj₁ (SN-lemma N⇓ (hi (B , n) (right (m<′n⊔m+1 n m))) N:α P⇓) σ⇂N Unyσ x:B
          in exp Mσ→Nσ Nσ⇓
        thesis₂ : (∃ λ γ → α ≡ B ⟶ γ) → Γ ⊢ P ∶ B → SN (M · P)
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
