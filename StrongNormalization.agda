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
open import ListProperties
open import Relation using (just)

open import Data.Nat hiding (_*_)
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Induction.WellFounded
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Relation.Nullary
open import Induction.Nat
open import Data.Nat.Properties

data _ₜ<_ : Type → Type → Set where
  ₜ<l : ∀ {α β} → α ₜ< (α ⇒ β)
  ₜ<r : ∀ {α β} → β ₜ< (α ⇒ β)

wfₜ< : Well-founded _ₜ<_
wfₜ< τ = acc λ y ()
wfₜ< (α ⇒ B) = acc wfₜ<-aux
  where wfₜ<-aux : (γ : Type) → γ ₜ< (α ⇒ B) → Acc _ₜ<_ γ
        wfₜ<-aux .α ₜ<l = wfₜ< α
        wfₜ<-aux .B ₜ<r = wfₜ< B
        
open Transitive-closure _ₜ<_ renaming (_<⁺_ to _ₜ<⁺_)

wfₜ<⁺ : Well-founded _ₜ<⁺_ 
wfₜ<⁺ = well-founded wfₜ<

open Lexicographic _ₜ<⁺_ (λ _ m n → m <′ n) renaming (_<_ to _ₜ,ₙ<_ ; well-founded to wfΣ)

wfₜ,ₙ< : Well-founded _ₜ,ₙ<_
wfₜ,ₙ< = wfΣ wfₜ<⁺ <-well-founded

IsVar : Λ → Set
IsVar M = ∃ λ y → M ≡ v y

SN′ : Λ → Set 
SN′ M = ∃ λ n → SN n M

_→SN′_ : Λ → Λ → Set 
M →SN′ N = ∃ λ n → M →SN n , N

Ren : Σ → Type → Cxt → Set
Ren σ α Γ = ∀ {x} → IsVar (σ x) ⊎ SN′ (σ x) × (Γ ⊢ v x ∶ α)

lemma-Renι : ∀ {x n α Γ M} → SN n M → Γ ⊢ M ∶ α → Ren (ι ≺+ (x , M)) α (Γ ‚ x ∶ α)
lemma-Renι {x} M⇓ M:α {y} with x ≟ y 
lemma-Renι {x} {n} M⇓ M:α .{x} | yes refl = inj₂ ((n , M⇓) , ⊢v (here refl))
... | no _ = inj₁ (y , refl)

lemma-Ren≺+ : ∀ {x z α Γ M σ β n} → Ren σ β Γ → SN n M → Ren (σ ≺+ (x , v z)) β (Γ ‚ x ∶ α)
lemma-Ren≺+ {x} {z} Πσ M⇓ {y} with x ≟ y
lemma-Ren≺+ {x} {z} Πσ M⇓ .{x} | yes refl = inj₁ (z , refl)
... | no x≢y with Πσ {y}
... | inj₁ isvar = inj₁ isvar
... | inj₂ (σy⇓ , Γ⊢y:β) = inj₂ (σy⇓ , lemmaWeakening⊢# (#v (sym≢ x≢y)) Γ⊢y:β)

SN-lemma-α : ∀ {M N n} → SN n M → M ∼α N → SN n N
SN-lemma-α = {!!}

hd : ∀ {M n} → SNe n M → V
hd (v {x}) = x
hd (app M⇓ _) = hd M⇓ 

SNe-preservedby-σ : ∀ {σ M n k} → (M⇓ : SNe n M) → IsVar (σ (hd M⇓)) → SN k (M ∙ σ) → SNe k (M ∙ σ)
SNe-preservedby-σ _ isvar Mσ⇓ = {!!}

lemma-≡Γx : ∀ {α β Γ x} → Γ ⊢ v x ∶ α → Γ ⊢ v x ∶ β → α ≡ β
lemma-≡Γx (⊢v x∈Γ₁) (⊢v x∈Γ₂) = lemma∈!⟨⟩ x∈Γ₁ x∈Γ₂

lemma-ₜ≤ : ∀ {α β Γ M n} → (M⇓ : SNe n M) → Γ ⊢ v (hd M⇓) ∶ β → Γ ⊢ M ∶ α → α ₜ<⁺ β ⊎ α ≡ β 
lemma-ₜ≤  v hdM:β hdM:α = inj₂ (lemma-≡Γx hdM:α hdM:β)
lemma-ₜ≤  {α} {B} (app M⇓ _) hdM:β (⊢· M:γ→α _) with lemma-ₜ≤ M⇓ hdM:β M:γ→α
... | inj₁ γ→α<β = inj₁ (trans [ ₜ<r ] γ→α<β)
lemma-ₜ≤ {α} .{γ ⇒ α} (app M⇓ _) hdM:β (⊢· {γ} M:γ→α _) | inj₂ refl = inj₁ [ ₜ<r ]

lemma-ₜ< : ∀ {α γ β Γ M n} → (M⇓ : SNe n M) → Γ ⊢ v (hd M⇓) ∶ β → Γ ⊢ M ∶ α ⇒ γ → α ₜ<⁺ β
lemma-ₜ< M⇓ hdM:β M:α→γ with lemma-ₜ≤ M⇓ hdM:β M:α→γ 
... | inj₁ α→γ<β = trans [ ₜ<l ] α→γ<β
lemma-ₜ< {α} {γ} .{α ⇒ γ} M⇓ hdM:β M:α→γ | inj₂ refl = [ ₜ<l ]

→SN⊂→β : ∀ {M N n} → M →SN n , N → M →β N 
→SN⊂→β (β _)  = ctxinj ▹β
→SN⊂→β (appl M→M') = ctx·l (→SN⊂→β M→M')

lemmaσ⇂· : ∀ {σ Γ Δ P Q} → σ ∶ Γ ⇀ Δ ⇂ P · Q → (σ ∶ Γ ⇀ Δ ⇂ P) × (σ ∶ Γ ⇀ Δ ⇂ Q)
lemmaσ⇂· σ⇂PQ = (λ x*P → σ⇂PQ (*·l x*P)) , (λ x*Q → σ⇂PQ (*·r x*Q))

m<′m⊔n+1 : ∀ m n → m <′ suc (m ⊔ n)
m<′m⊔n+1 m n = s≤′s (≤⇒≤′ (m≤m⊔n m n))

m<′n⊔m+1 : ∀ m n → m <′ suc (n ⊔ m)
m<′n⊔m+1 = {!!}

SN-lemma : ∀ {M Γ α β n}
         → Acc _ₜ,ₙ<_ (β , n)
         → SN n M
         → Γ ⊢ M ∶ α
         → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Ren σ β Γ → SN′ (M ∙ σ))
           × (∀ {N k} → SN k N → Γ ⊢ N ∶ β → (∃ λ γ → α ≡ β ⇒ γ) → SN′ (M · N)) 

SN-lemma→ : ∀ {L K σ Γ Δ α β n}
          → Acc _ₜ,ₙ<_ (β , n)
          → L →SN n , K
          → Γ ⊢ L ∶ α
          → σ ∶ Γ ⇀ Δ ⇂ L
          → Ren σ β Γ
          → ∃ λ P → (L ∙ σ) →SN′ P × P ∼α K ∙ σ

SN-lemmaNe : ∀ {M Γ α β n}
           → Acc _ₜ,ₙ<_ (β , n)
           → SNe n M
           → Γ ⊢ M ∶ α
           → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Ren σ β Γ → SN′ (M ∙ σ))
             × (∀ {N k} → SN k N → Γ ⊢ N ∶ β → (∃ λ γ → α ≡ β ⇒ γ) → SN′ (M · N))

SN-lemma→ {ƛ x L · J} {_} {σ} {Γ} {Δ} {α} {B} {suc n} (acc hi) (β J⇓) (⊢· _ J:γ) σ⇂ƛxLJ Πσ =
  let z : V
      z = χ (σ , ƛ x L)
      L[σ,x=z][z=Jσ]~L[x=J]σ : L [ σ ∣ x := v z ] [ z := J ∙ σ ] ∼α L [ x := J ] ∙ σ
      L[σ,x=z][z=Jσ]~L[x=J]σ = lemma∼α∙ (χ-lemma2 σ (ƛ x L))
      σ⇂J : σ ∶ Γ ⇀ Δ ⇂ J
      σ⇂J = proj₂ (lemmaσ⇂· σ⇂ƛxLJ)
      --Jσ⇓ : SN′ (J ∙ σ)
      k , Jσ⇓ = proj₁ (SN-lemma (hi (B , n) (right ≤′-refl)) J⇓ J:γ) σ⇂J Πσ
  in L [ σ ∣ x := v z ] [ z := J ∙ σ ] , (suc k , β Jσ⇓) , L[σ,x=z][z=Jσ]~L[x=J]σ
SN-lemma→ {L · J} {L' · .J} {σ} {Γ} {Δ} {_} {B} {suc n} (acc hi) (appl L→L') (⊢· L:γ _) σ⇂LJ Πσ =
  let σ⇂L : σ ∶ Γ ⇀ Δ ⇂ L
      σ⇂L = proj₁ (lemmaσ⇂· σ⇂LJ)
      P , (k , Lσ→P) , P~L'σ = SN-lemma→ (hi (B , n) (right ≤′-refl)) L→L' L:γ σ⇂L Πσ
      PJσ~L'Jσ : P · (J ∙ σ) ∼α L' · J ∙ σ 
      PJσ~L'Jσ = ∼· P~L'σ ∼ρ
      LJσ→PJσ : L · J ∙ σ →SN (suc k) , P · (J ∙ σ)
      LJσ→PJσ = appl Lσ→P
  in P · (J ∙ σ) , (suc k , LJσ→PJσ) , PJσ~L'Jσ

SN-lemmaNe .{v x} {Γ} {_} {B} _ (v {x}) _ = thesis₁ , λ {_} {k} N⇓ _ _ → suc (suc k) , sne (app v N⇓)
  where thesis₁ : ∀ {σ} {Δ} → σ ∶ Γ ⇀ Δ ⇂ (v x) → Ren σ B Γ → SN′ (v x ∙ σ)
        thesis₁ {σ} _ Πσ with σ x | Πσ {x} 
        ... | .(v y) | inj₁ (y , refl) = 1 , sne v
        ... | _ | inj₂ (σx⇓ , _) = σx⇓ 
SN-lemmaNe {P · Q} {Γ} {_} {B} (acc hi) (app {m = m} {n = n} P⇓ Q⇓) (⊢· {γ} {ε} P:γ→ε Q:γ) =
  thesis₁ , λ {_} {k} N⇓ _ _ → suc (suc ((suc (m ⊔ n)) ⊔ k))  , sne (app (app P⇓ Q⇓) N⇓)
    where
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ P · Q → Ren σ B Γ → SN′ (P · Q ∙ σ)
        thesis₁ {σ} {Δ} σ⇂PQ Πσ =
          let σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
              σ⇂P = λ x*P → σ⇂PQ (*·l x*P)
              --Pσ⇓ : SN (P ∙ σ)
              p , Pσ⇓ = proj₁ (SN-lemmaNe (hi (B , m) (right (m<′m⊔n+1 m n))) P⇓ P:γ→ε) σ⇂P Πσ
              σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
              σ⇂Q = λ x*Q → σ⇂PQ (*·r x*Q)
              --Qσ⇓ : SN (Q ∙ σ)
              q , Qσ⇓ = proj₁ (SN-lemma (hi (B , n) (right (m<′n⊔m+1 n m))) Q⇓ Q:γ) σ⇂Q Πσ
              Pσ:γ→ε : Δ ⊢ P ∙ σ ∶ γ ⇒ ε
              Pσ:γ→ε = lemma⊢σM P:γ→ε σ⇂P                                                                            
              Qσ:γ : Δ ⊢ Q ∙ σ ∶ γ 
              Qσ:γ = lemma⊢σM Q:γ σ⇂Q
              PQσ⇓₁ = λ isVar → suc (suc (p ⊔ q)) , sne (app (SNe-preservedby-σ {σ} {P} P⇓ isVar Pσ⇓) Qσ⇓)
              PQσ⇓₂ = λ { (_ , hdP:β) →
                let γ<β : γ ₜ<⁺ B
                    γ<β = lemma-ₜ< P⇓ hdP:β P:γ→ε
                    --accγ : Acc _ₜ<⁺_ γ
                    --accγ = hiₜ γ γ<β
                in proj₂ (SN-lemma (hi (γ , p) (left γ<β)) Pσ⇓ Pσ:γ→ε) Qσ⇓ Qσ:γ (ε , refl) }
          in [ PQσ⇓₁ , PQσ⇓₂ ]′ (Πσ {hd P⇓})
                                  
SN-lemma {β = B} (acc hi) (sne {m = m} M⇓) = SN-lemmaNe (hi (B , m) (right ≤′-refl)) M⇓ 
SN-lemma {ƛ x P} {Γ} {δ ⇒ ε} {B} (acc hi) (abs {m = m} P⇓) (⊢ƛ P:ε) = thesis₁ , thesis₂ (⊢ƛ P:ε)
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ ƛ x P → Ren σ B Γ → SN′ (ƛ x P ∙ σ)
        thesis₁ {σ} {Δ} σ⇂ƛxP Πσ =
          let z : V
              z = χ (σ , ƛ x P)
              σ⇂P : (σ ≺+ (x , v z)) ∶ (Γ ‚ x ∶ δ) ⇀ (Δ ‚ z ∶ δ)  ⇂ P
              σ⇂P = lemmaaux⇀ (χ-lemma2 σ (ƛ x P)) σ⇂ƛxP
              Πσ,x=z : Ren (σ ≺+ (x , v z)) B (Γ ‚ x ∶ δ)
              Πσ,x=z = lemma-Ren≺+ Πσ P⇓
              k , Pσ,x=z⇓ = proj₁ (SN-lemma (hi (B , m) (right ≤′-refl)) P⇓ P:ε) σ⇂P Πσ,x=z
          in suc k , abs Pσ,x=z⇓
        thesis₂ : ∀ {N δ ε n} → Γ ⊢ ƛ x P ∶ δ ⇒ ε → SN n N → Γ ⊢ N ∶ B → (∃ λ γ → δ ⇒ ε ≡ B ⇒ γ) → SN′ (ƛ x P · N)
        thesis₂ {N} {.B} {.γ} {n} (⊢ƛ P:γ) N⇓ N:B (γ , refl) =
          let x=N⇂P : (ι ≺+ (x , N)) ∶ (Γ ‚ x ∶ B) ⇀ Γ ⇂ P
              x=N⇂P = lemma⇀ (lemmaι≺+⇀ N:B)
              Πx=N : Ren (ι ≺+ (x ∶ N)) B (Γ ‚ x ∶ B)
              Πx=N = lemma-Renι N⇓ N:B
              k , Px=N⇓ = proj₁ (SN-lemma (hi (B , m) (right ≤′-refl)) P⇓ P:γ) x=N⇂P Πx=N
          in suc ((suc n) ⊔ k) , exp (β N⇓) Px=N⇓
SN-lemma {M} {Γ} {α} {B} (acc hi) (exp {.M} {N} {m} {n} M→N N⇓) M:α = thesis₁ , thesis₂
  where M→βN : M →β N
        M→βN = →SN⊂→β M→N
        N:α : Γ ⊢ N ∶ α
        N:α = lemma⊢→α* M:α (just (inj₁ M→βN))
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Ren σ B Γ → SN′ (M ∙ σ)
        thesis₁ {σ} {Δ} σ⇂M Πσ =
          let _ , (k , Mσ→P) , P~Nσ = SN-lemma→ (hi (B , m) (right (m<′m⊔n+1 m n))) M→N M:α σ⇂M Πσ
              σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
              σ⇂N = λ x*N → σ⇂M (lemma→α* x*N M→βN)
              --Nσ⇓ : SN′ (N ∙ σ)
              l , Nσ⇓ = proj₁ (SN-lemma (hi (B , n) (right (m<′n⊔m+1 n m))) N⇓ N:α) σ⇂N Πσ
          in suc (k ⊔ l) , exp Mσ→P (SN-lemma-α Nσ⇓ (∼σ P~Nσ))
        thesis₂ : ∀ {P n} → SN n P → Γ ⊢ P ∶ B → (∃ λ γ → α ≡ B ⇒ γ) → SN′ (M · P)
        thesis₂ P⇓ P:B α=β→γ =
          let k , NP⇓ = proj₂ (SN-lemma (hi (B , n) (right (m<′n⊔m+1 n m))) N⇓ N:α) P⇓ P:B α=β→γ
          in suc ((suc m) ⊔ k) , exp (appl M→N) NP⇓ 

SN-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → SN′ M
SN-theo (⊢v _) = 1 , sne v
SN-theo (⊢· {α} {B} {M} M:α→β N:α) =
  let m , M⇓ = SN-theo M:α→β
      _ , N⇓ = SN-theo N:α
  in proj₂ (SN-lemma (wfₜ,ₙ< (α , m)) M⇓ M:α→β) N⇓ N:α (B , refl)
SN-theo (⊢ƛ M:α) =
  let m , M⇓ = SN-theo M:α
  in suc m , abs M⇓ 

sn-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
sn-theo M:α = sound-SN (proj₂ (SN-theo M:α))
