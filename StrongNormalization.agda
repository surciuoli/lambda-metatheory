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
open import Relation using (just)

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

-- Definitions

data IsVar : Λ → Set where
  isv : ∀ {x} → IsVar (v x)

Ren : Σ → Set
Ren σ = ∀ {x} → IsVar (σ x)

Unary : Σ → Type → Cxt → Set
Unary σ α Γ = ∀ {x} → IsVar (σ x) ⊎ SN (σ x) × (Γ ⊢ v x ∶ α)

hd : ∀ {M} → SNe M → V
hd (v {x}) = x
hd (app M⇓ _) = hd M⇓ 

height→   : ∀ {M N} → M →SN N → ℕ 
heightNe  : ∀ {M} → SNe M → ℕ 
height    : ∀ {M} → SN M → ℕ 

height→ (β N⇓) = suc (height N⇓)
height→ (appl M→N) = suc (height→ M→N)

heightNe v = 0
heightNe (app M⇓ N⇓) = suc (heightNe M⇓ ⊔ height N⇓)

height (abs M⇓) = suc (height M⇓)
height (sne M⇓) = suc (heightNe M⇓)
height (exp M→N N⇓) = suc (height→ M→N ⊔ height N⇓)

-- Auxiliary lemmas

lemma< : ∀ {m n p} → m ≡ n → n <′ p → m <′ p
lemma< refl n<p = n<p

lemma≡suc : ∀ {m n} → m ≡ n → suc m ≡ suc n
lemma≡suc refl = refl

lemma≡⊔ : ∀ {m n p q} → m ≡ n → p ≡ q → m ⊔ p ≡ n ⊔ q
lemma≡⊔ refl refl = refl

m<′m⊔n+1 : ∀ m n → m <′ suc (m ⊔ n)
m<′m⊔n+1 m n = s≤′s (≤⇒≤′ (m≤m⊔n m n))

⊔-comm = IsCommutativeMonoid.comm (IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid ⊔-⊓-0-isCommutativeSemiringWithoutOne)

m<′n⊔m+1 : ∀ m n → m <′ suc (n ⊔ m)
m<′n⊔m+1 m n with n ⊔ m | ⊔-comm n m
m<′n⊔m+1 m n | .(m ⊔ n) | refl = m<′m⊔n+1 m n

Renι : Ren ι
Renι = isv

Ren≺+ : ∀ {π} x y → Ren π → Ren (π ≺+ (x , v y))
Ren≺+ x y Renπ {w} with x ≟ w
Ren≺+ x y Renπ {.x} | yes refl = isv
... | no _ = Renπ {w}

lemma-Unaryι : ∀ {x α Γ M} → SN M → Γ ⊢ M ∶ α → Unary (ι ≺+ (x , M)) α (Γ ‚ x ∶ α)
lemma-Unaryι {x} M⇓ M:α {y} with x ≟ y 
lemma-Unaryι {x} M⇓ M:α .{x} | yes refl = inj₂ (M⇓ , ⊢v (here refl))
... | no _ = inj₁ isv 

lemma-Unary≺+ : ∀ {x z α Γ M σ β} → Unary σ β Γ → SN M → Unary (σ ≺+ (x , v z)) β (Γ ‚ x ∶ α)
lemma-Unary≺+ {x} {z} Πσ M⇓ {y} with x ≟ y
lemma-Unary≺+ {x} {z} Πσ M⇓ .{x} | yes refl = inj₁ isv 
... | no x≢y with Πσ {y}
... | inj₁ isvar = inj₁ isvar
... | inj₂ (σy⇓ , Γ⊢y:β) = inj₂ (σy⇓ , lemmaWeakening⊢# (#v (sym≢ x≢y)) Γ⊢y:β)

SN-lemma-α : ∀ {M N} → (M⇓ : SN M) → Acc _<′_ (height M⇓) → M ∼α N → Σₓ (SN N) λ N⇓ → height N⇓ ≡ height M⇓ 
SN-lemma-αNe : ∀ {M N} → (M⇓ : SNe M) → Acc _<′_ (heightNe M⇓) → M ∼α N → Σₓ (SNe N) λ N⇓ → heightNe N⇓ ≡ heightNe M⇓
SN-confl : ∀ {M N P} → M ∼α N → (N→P : N →SN P) → Acc _<′_ (height→ N→P) → ∃ λ Q → (Σₓ (M →SN Q) λ M→Q → height→ M→Q ≡ height→ N→P) × Q ∼α P
SN-preservedby-π : ∀ {M π} → Ren π → (M⇓ : SN M) → Acc _<′_ (height M⇓) → Σₓ (SN (M ∙ π)) λ Mπ⇓ → height Mπ⇓ ≡ height M⇓ 
SN-preservedby-πNe : ∀ {M π} → Ren π → (M⇓ : SNe M) → Acc _<′_ (heightNe M⇓) → Σₓ (SNe (M ∙ π)) λ Mπ⇓ → heightNe Mπ⇓ ≡ heightNe M⇓ 
Ren→compat : ∀ {M N π} → Ren π → (M→N : M →SN N) → Acc _<′_ (height→ M→N) → ∃ λ P → (Σₓ (M ∙ π →SN P) λ M→Nπ → height→ M→Nπ ≡ height→ M→N) × P ∼α N ∙ π

SN-preservedby-π Renπ (sne M⇓) (acc hi) =
  mapₓ sne lemma≡suc (SN-preservedby-πNe Renπ M⇓ (hi (heightNe M⇓) ≤′-refl))
SN-preservedby-π {ƛ x M} {π} Renπ (abs M⇓) (acc hi) =
  mapₓ abs lemma≡suc (SN-preservedby-π (Ren≺+ x (χ (π , ƛ x M)) Renπ) M⇓ (hi (height M⇓) ≤′-refl))
SN-preservedby-π Renπ (exp M→N N⇓) (acc hi) =
  let k , l =  height→ M→N , height N⇓
      _ , (Mπ→P , hMπ→P≡hM→N) , P~Nπ = Ren→compat Renπ M→N (hi k (m<′m⊔n+1 k l))
      Nπ⇓ , hNπ⇓≡hN⇓ = SN-preservedby-π Renπ N⇓ (hi l (m<′n⊔m+1 l k))
      P⇓ , hP⇓≡Nπ = SN-lemma-α Nπ⇓ (hi (height Nπ⇓) (lemma< hNπ⇓≡hN⇓ (m<′n⊔m+1 l k))) (∼σ P~Nπ)
  in exp Mπ→P P⇓ , lemma≡suc (lemma≡⊔ hMπ→P≡hM→N (trans≡ hP⇓≡Nπ hNπ⇓≡hN⇓))

SN-preservedby-πNe {v x} {π} Renπ v _ with π x | Renπ {x}
... | v y | isv {.y} = v {y} , refl
SN-preservedby-πNe Renπ (app M⇓ N⇓) (acc hi) =
  let m , n = heightNe M⇓ , height N⇓
      Mπ⇓ , hMπ≡hM = SN-preservedby-πNe Renπ M⇓ (hi m (m<′m⊔n+1 m n))
      Nπ⇓ , hNπ≡hN = SN-preservedby-π Renπ N⇓ (hi n (m<′n⊔m+1 n m))
  in app Mπ⇓ Nπ⇓ , lemma≡suc (lemma≡⊔ hMπ≡hM hNπ≡hN)

Ren→compat {ƛ x M · N} {_} {π} Renπ (β N⇓) (acc hi) =
  let z : V
      z = χ (π , ƛ x M)
      M[π,x=z][z=Nπ]~M[x=N]π : M [ π ∣ x := v z ] [ z := N ∙ π ] ∼α M [ x := N ] ∙ π 
      M[π,x=z][z=Nπ]~M[x=N]π = lemma∼α∙ (χ-lemma2 π (ƛ x M))
      --Nπ⇓ : SN (N ∙ π)
      Nπ⇓ , hNπ≡hN = SN-preservedby-π Renπ N⇓ (hi (height N⇓) ≤′-refl)
  in M [ π ∣ x := v z ] [ z := N ∙ π ] , (β Nπ⇓ , lemma≡suc hNπ≡hN) , M[π,x=z][z=Nπ]~M[x=N]π
Ren→compat {M · N} {M' · .N} {π} Renπ (appl M→M') (acc hi) = 
  let P , (Mπ→P , hMπ→P≡hM→N) , P~M'π = Ren→compat Renπ M→M' (hi (height→ M→M') ≤′-refl)
      PNπ~M'Nπ : P · (N ∙ π) ∼α M' · N ∙ π
      PNπ~M'Nπ = ∼· P~M'π ∼ρ
      MNπ→PNπ : M · N ∙ π →SN P · (N ∙ π)
      MNπ→PNπ = appl Mπ→P
  in P · (N ∙ π) , (MNπ→PNπ , lemma≡suc hMπ→P≡hM→N) , PNπ~M'Nπ
  
SN-lemma-α (sne M⇓) (acc hi) M~N =
  mapₓ sne lemma≡suc (SN-lemma-αNe M⇓ (hi (heightNe M⇓) ≤′-refl) M~N)
SN-lemma-α {ƛ x M} {ƛ y N} (abs M⇓) (acc hi) (∼ƛ z#M z#N M∼N) =
  mapₓ abs (λ hN≡hMπ → lemma≡suc (trans≡ hN≡hMπ hMπ≡hM)) (SN-lemma-α Mπ⇓ (hi (height Mπ⇓) (lemma< hMπ≡hM ≤′-refl)) Mπ~N)
    where π : Σ
          π = ι ≺+ (x , v y)
          Renπ : Ren π
          Renπ = Ren≺+ x y Renι
          Mxh : Σₓ (SN (M ∙ π)) λ Mπ⇓ → height Mπ⇓ ≡ height M⇓ 
          Mxh = SN-preservedby-π Renπ M⇓ (hi (height M⇓) ≤′-refl)
          Mπ⇓ : SN (M ∙ π) 
          Mπ⇓ = proj₁ Mxh
          hMπ≡hM : height Mπ⇓ ≡ height M⇓ 
          hMπ≡hM = proj₂ Mxh
          Mπ~N : M ∙ π ∼α N
          Mπ~N = lemma-α-ren (∼ƛ z#M z#N M∼N)
SN-lemma-α (exp M→N N⇓) (acc hi) M~P =
  let k , l =  height→ M→N , height N⇓
      _ , (P→Q , hP→Q≡hM→N) , Q~N = SN-confl (∼σ M~P) M→N (hi k (m<′m⊔n+1 k l))
      Q⇓ , hQ≡hN = SN-lemma-α N⇓ (hi l (m<′n⊔m+1 l k)) (∼σ Q~N) 
  in exp P→Q Q⇓ , lemma≡suc (lemma≡⊔ hP→Q≡hM→N hQ≡hN)

SN-lemma-αNe v _ ∼v = v , refl
SN-lemma-αNe (app M⇓ N⇓) (acc hi) (∼· M~M' N~N') =
  let m , n = heightNe M⇓ , height N⇓
      (M'⇓ , hM'≡hM) , (N'⇓ , hN'≡hN) = SN-lemma-αNe M⇓ (hi m (m<′m⊔n+1 m n)) M~M' , SN-lemma-α N⇓ (hi n (m<′n⊔m+1 n m)) N~N'
  in app M'⇓ N'⇓ , lemma≡suc (lemma≡⊔ hM'≡hM hN'≡hN)
  
SN-confl {ƛ x M · N} {ƛ y M' · N'} .{M' [ y := N' ]} (∼· (∼ƛ z#M z#M' M∼M') N~N') (β N'⇓) (acc hi) =
  M [ x := N ] , mapₓ β lemma≡suc (SN-lemma-α N'⇓ (hi (height N'⇓) ≤′-refl) (∼σ N~N')), β-equiv (∼· (∼ƛ z#M z#M' M∼M') N~N')
SN-confl {M · N} {M' · N'} {M'' · .N'} (∼· M~M' N~N') (appl M'→M'') (acc hi) =
  let P , (M→P , hM'→M''≡hM→P) , P~M'' = SN-confl M~M' M'→M'' (hi (height→ M'→M'') ≤′-refl)
  in P · N , (appl M→P , lemma≡suc hM'→M''≡hM→P) , ∼· P~M'' N~N'
  
SNe-reduces⇒⊥ : ∀ {σ M N} → (M⇓ : SNe M) → IsVar (σ (hd M⇓)) → M ∙ σ →SN N → ⊥
SNe-reduces⇒⊥ {σ} (v {x}) isvar Mσ→N with σ x
SNe-reduces⇒⊥ {σ} (v {x}) (isv {y}) () | v {.y}
SNe-reduces⇒⊥ {σ} (app (v {x}) _) isvar xPσ→N with σ x
SNe-reduces⇒⊥ {σ} (app (v {x}) _) (isv {y}) (appl yPσ→N) | v {.y} = SNe-reduces⇒⊥ (v {x}) (isv {y}) yPσ→N
SNe-reduces⇒⊥ (app M⇓ _) isvar (appl Mσ→Nσ) = SNe-reduces⇒⊥ M⇓ isvar Mσ→Nσ

SNe-preservedby-σ : ∀ {σ M} → (M⇓ : SNe M) → IsVar (σ (hd M⇓)) → SN (M ∙ σ) → SNe (M ∙ σ)
SNe-preservedby-σ {σ} (v {x}) isvar Mσ⇓ with σ x
SNe-preservedby-σ {σ} (v {x}) (isv {y}) (sne (v {.y})) | (v {.y}) = v {y}
SNe-preservedby-σ {σ} (v {x}) (isv {y}) (exp () _) | (v {.y})
SNe-preservedby-σ {σ} (app P⇓ Q⇓) isvar (sne (app Pσ⇓ Qσ⇓)) = app Pσ⇓ Qσ⇓
SNe-preservedby-σ {σ} M⇓ isvar (exp M→N _) = ⊥-elim (SNe-reduces⇒⊥ M⇓ isvar M→N)

lemma-≡Γx : ∀ {α β Γ x} → Γ ⊢ v x ∶ α → Γ ⊢ v x ∶ β → α ≡ β
lemma-≡Γx (⊢v x∈Γ₁) (⊢v x∈Γ₂) = lemma∈!⟨⟩ x∈Γ₁ x∈Γ₂

lemma-ₜ≤ : ∀ {α β Γ M} → (M⇓ : SNe M) → Γ ⊢ v (hd M⇓) ∶ β → Γ ⊢ M ∶ α → α ₜ<⁺ β ⊎ α ≡ β 
lemma-ₜ≤  v hdM:β hdM:α = inj₂ (lemma-≡Γx hdM:α hdM:β)
lemma-ₜ≤  {α} {B} (app M⇓ _) hdM:β (⊢· M:γ→α _) with lemma-ₜ≤ M⇓ hdM:β M:γ→α
... | inj₁ γ→α<β = inj₁ (trans [ ₜ<r ] γ→α<β)
lemma-ₜ≤ {α} .{γ ⇒ α} (app M⇓ _) hdM:β (⊢· {γ} M:γ→α _) | inj₂ refl = inj₁ [ ₜ<r ]

lemma-ₜ< : ∀ {α γ β Γ M} → (M⇓ : SNe M) → Γ ⊢ v (hd M⇓) ∶ β → Γ ⊢ M ∶ α ⇒ γ → α ₜ<⁺ β
lemma-ₜ< M⇓ hdM:β M:α→γ with lemma-ₜ≤ M⇓ hdM:β M:α→γ 
... | inj₁ α→γ<β = trans [ ₜ<l ] α→γ<β
lemma-ₜ< {α} {γ} .{α ⇒ γ} M⇓ hdM:β M:α→γ | inj₂ refl = [ ₜ<l ]

→SN⊂→β : ∀ {M N} → M →SN N → M →β N 
→SN⊂→β (β _)  = ctxinj ▹β
→SN⊂→β (appl M→M') = ctx·l (→SN⊂→β M→M')

lemmaσ⇂· : ∀ {σ Γ Δ P Q} → σ ∶ Γ ⇀ Δ ⇂ P · Q → (σ ∶ Γ ⇀ Δ ⇂ P) × (σ ∶ Γ ⇀ Δ ⇂ Q)
lemmaσ⇂· σ⇂PQ = (λ x*P → σ⇂PQ (*·l x*P)) , (λ x*Q → σ⇂PQ (*·r x*Q))

-- Main lemma

SN-lemma : ∀ {M Γ α β n}
         → Acc _ₜ,ₙ<_ (β , n)
         → (M⇓ : SN M)
         → n ≡ height M⇓ 
         → Γ ⊢ M ∶ α
         → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ β Γ → SN (M ∙ σ))
           × (∀ {N} → SN N → Γ ⊢ N ∶ β → (∃ λ γ → α ≡ β ⇒ γ) → SN (M · N)) 

SN-lemma→ : ∀ {L K σ Γ Δ α β n}
          → Acc _ₜ,ₙ<_ (β , n)
          → (M→N : L →SN K)
          → n ≡ height→ M→N
          → Γ ⊢ L ∶ α
          → σ ∶ Γ ⇀ Δ ⇂ L
          → Unary σ β Γ
          → ∃ λ P → (L ∙ σ) →SN P × P ∼α K ∙ σ

SN-lemmaNe : ∀ {M Γ α β n}
           → Acc _ₜ,ₙ<_ (β , n)
           → (M⇓ : SNe M)
           → n ≡ heightNe M⇓ 
           → Γ ⊢ M ∶ α
           → (∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ β Γ → SN (M ∙ σ))
             × (∀ {N} → SN N → Γ ⊢ N ∶ β → (∃ λ γ → α ≡ β ⇒ γ) → SN (M · N))

SN-lemma→ {ƛ x L · J} {_} {σ} {Γ} {Δ} {α} {B} .{suc (height J⇓)} (acc hi) (β J⇓) refl (⊢· _ J:γ) σ⇂ƛxLJ Πσ =
  let z : V
      z = χ (σ , ƛ x L)
      L[σ,x=z][z=Jσ]~L[x=J]σ : L [ σ ∣ x := v z ] [ z := J ∙ σ ] ∼α L [ x := J ] ∙ σ
      L[σ,x=z][z=Jσ]~L[x=J]σ = lemma∼α∙ (χ-lemma2 σ (ƛ x L))
      σ⇂J : σ ∶ Γ ⇀ Δ ⇂ J
      σ⇂J = proj₂ (lemmaσ⇂· σ⇂ƛxLJ)
      Jσ⇓ : SN (J ∙ σ)
      Jσ⇓ = proj₁ (SN-lemma (hi (B , height J⇓) (right ≤′-refl)) J⇓ refl J:γ) σ⇂J Πσ
  in L [ σ ∣ x := v z ] [ z := J ∙ σ ] , β Jσ⇓ , L[σ,x=z][z=Jσ]~L[x=J]σ
SN-lemma→ {L · J} {L' · .J} {σ} {Γ} {Δ} {_} {B} .{suc (height→ L→L')} (acc hi) (appl L→L') refl (⊢· L:γ _) σ⇂LJ Πσ =
  let σ⇂L : σ ∶ Γ ⇀ Δ ⇂ L
      σ⇂L = proj₁ (lemmaσ⇂· σ⇂LJ)
      P , Lσ→P , P~L'σ = SN-lemma→ (hi (B , height→ L→L') (right ≤′-refl)) L→L' refl L:γ σ⇂L Πσ
      PJσ~L'Jσ : P · (J ∙ σ) ∼α L' · J ∙ σ 
      PJσ~L'Jσ = ∼· P~L'σ ∼ρ
      LJσ→PJσ : L · J ∙ σ →SN P · (J ∙ σ)
      LJσ→PJσ = appl Lσ→P
  in P · (J ∙ σ) , LJσ→PJσ , PJσ~L'Jσ

SN-lemmaNe .{v x} {Γ} {_} {B} .{0} _ (v {x}) refl _  = thesis₁ , λ N⇓ _ _ → sne (app v N⇓)
  where thesis₁ : ∀ {σ} {Δ} → σ ∶ Γ ⇀ Δ ⇂ (v x) → Unary σ B Γ → SN (v x ∙ σ)
        thesis₁ {σ} _ Πσ with σ x | Πσ {x} 
        ... | .(v y) | inj₁ (isv {y}) = sne v
        ... | _ | inj₂ (σx⇓ , _) = σx⇓ 
SN-lemmaNe {P · Q} {Γ} {_} {B} .{suc (heightNe P⇓ ⊔ height Q⇓) } (acc hi) (app P⇓ Q⇓) refl (⊢· {γ} {ε} P:γ→ε Q:γ) =
  thesis₁ , λ N⇓ _ _ → sne (app (app P⇓ Q⇓) N⇓)
    where
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ P · Q → Unary σ B Γ → SN (P · Q ∙ σ)
        thesis₁ {σ} {Δ} σ⇂PQ Πσ =
          let m , n = heightNe P⇓ , height Q⇓
              σ⇂P : σ ∶ Γ ⇀ Δ ⇂ P
              σ⇂P = λ x*P → σ⇂PQ (*·l x*P)
              Pσ⇓ : SN (P ∙ σ)
              Pσ⇓ = proj₁ (SN-lemmaNe (hi (B , m) (right (m<′m⊔n+1 m n))) P⇓ refl P:γ→ε) σ⇂P Πσ
              σ⇂Q : σ ∶ Γ ⇀ Δ ⇂ Q
              σ⇂Q = λ x*Q → σ⇂PQ (*·r x*Q)
              Qσ⇓ : SN (Q ∙ σ)
              Qσ⇓ = proj₁ (SN-lemma (hi (B , n) (right (m<′n⊔m+1 n m))) Q⇓ refl Q:γ) σ⇂Q Πσ
              Pσ:γ→ε : Δ ⊢ P ∙ σ ∶ γ ⇒ ε
              Pσ:γ→ε = lemma⊢σM P:γ→ε σ⇂P                                                                            
              Qσ:γ : Δ ⊢ Q ∙ σ ∶ γ 
              Qσ:γ = lemma⊢σM Q:γ σ⇂Q
              PQσ⇓₁ = λ isVar → sne (app (SNe-preservedby-σ {σ} {P} P⇓ isVar Pσ⇓) Qσ⇓)
              PQσ⇓₂ = λ { (_ , hdP:β) →
                let γ<β : γ ₜ<⁺ B
                    γ<β = lemma-ₜ< P⇓ hdP:β P:γ→ε
                in proj₂ (SN-lemma (hi (γ , height Pσ⇓) (left γ<β)) Pσ⇓ refl Pσ:γ→ε) Qσ⇓ Qσ:γ (ε , refl) }
          in [ PQσ⇓₁ , PQσ⇓₂ ]′ (Πσ {hd P⇓})
                                  
SN-lemma {β = B} .{n = suc (heightNe M⇓)} (acc hi) (sne M⇓) refl = SN-lemmaNe (hi (B , heightNe M⇓) (right ≤′-refl)) M⇓ refl
SN-lemma {ƛ x P} {Γ} {δ ⇒ ε} {B} .{suc (height P⇓)} (acc hi) (abs P⇓) refl (⊢ƛ P:ε) = thesis₁ , thesis₂ (⊢ƛ P:ε)
  where thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ ƛ x P → Unary σ B Γ → SN (ƛ x P ∙ σ)
        thesis₁ {σ} {Δ} σ⇂ƛxP Πσ =
          let z : V
              z = χ (σ , ƛ x P)
              σ⇂P : (σ ≺+ (x , v z)) ∶ (Γ ‚ x ∶ δ) ⇀ (Δ ‚ z ∶ δ)  ⇂ P
              σ⇂P = lemmaaux⇀ (χ-lemma2 σ (ƛ x P)) σ⇂ƛxP
              Πσ,x=z : Unary (σ ≺+ (x , v z)) B (Γ ‚ x ∶ δ)
              Πσ,x=z = lemma-Unary≺+ Πσ P⇓
              Pσ,x=z⇓ = proj₁ (SN-lemma (hi (B , height P⇓) (right ≤′-refl)) P⇓ refl P:ε) σ⇂P Πσ,x=z
          in abs Pσ,x=z⇓
        thesis₂ : ∀ {N δ ε} → Γ ⊢ ƛ x P ∶ δ ⇒ ε → SN N → Γ ⊢ N ∶ B → (∃ λ γ → δ ⇒ ε ≡ B ⇒ γ) → SN (ƛ x P · N)
        thesis₂ {N} {.B} {.γ} (⊢ƛ P:γ) N⇓ N:B (γ , refl) =
          let x=N⇂P : (ι ≺+ (x , N)) ∶ (Γ ‚ x ∶ B) ⇀ Γ ⇂ P
              x=N⇂P = lemma⇀ (lemmaι≺+⇀ N:B)
              Πx=N : Unary (ι ≺+ (x ∶ N)) B (Γ ‚ x ∶ B)
              Πx=N = lemma-Unaryι N⇓ N:B
              Px=N⇓ = proj₁ (SN-lemma (hi (B , height P⇓) (right ≤′-refl)) P⇓ refl P:γ) x=N⇂P Πx=N
          in exp (β N⇓) Px=N⇓
SN-lemma {M} {Γ} {α} {B} .{n = suc (height→ M→N ⊔ height N⇓)} (acc hi) (exp {.M} {N} M→N N⇓) refl M:α = thesis₁ , thesis₂
  where m = height→ M→N
        n = height N⇓ 
        M→βN : M →β N
        M→βN = →SN⊂→β M→N
        N:α : Γ ⊢ N ∶ α
        N:α = lemma⊢→α* M:α (just (inj₁ M→βN))
        thesis₁ : ∀ {σ Δ} → σ ∶ Γ ⇀ Δ ⇂ M → Unary σ B Γ → SN (M ∙ σ)
        thesis₁ {σ} {Δ} σ⇂M Πσ =
          let _ , Mσ→P , P~Nσ = SN-lemma→ (hi (B , m) (right (m<′m⊔n+1 m n))) M→N refl M:α σ⇂M Πσ
              σ⇂N : σ ∶ Γ ⇀ Δ ⇂ N
              σ⇂N = λ x*N → σ⇂M (lemma→α* x*N M→βN)
              Nσ⇓ : SN (N ∙ σ)
              Nσ⇓ = proj₁ (SN-lemma (hi (B , n) (right (m<′n⊔m+1 n m))) N⇓ refl N:α) σ⇂N Πσ
          in exp Mσ→P (proj₁ (SN-lemma-α Nσ⇓ (<-well-founded (height Nσ⇓)) (∼σ P~Nσ)))
        thesis₂ : ∀ {P} → SN P → Γ ⊢ P ∶ B → (∃ λ γ → α ≡ B ⇒ γ) → SN (M · P)
        thesis₂ P⇓ P:B α=β→γ =
          let NP⇓ = proj₂ (SN-lemma (hi (B , n) (right (m<′n⊔m+1 n m))) N⇓ refl N:α) P⇓ P:B α=β→γ
          in exp (appl M→N) NP⇓ 

SN-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → SN M
SN-theo (⊢v _) = sne v
SN-theo (⊢· {α} {B} {M} M:α→β N:α) =
  let M⇓ = SN-theo M:α→β
  in proj₂ (SN-lemma (wfₜ,ₙ< (α , height M⇓)) M⇓ refl M:α→β) (SN-theo N:α) N:α (B , refl)
SN-theo (⊢ƛ M:α) = abs (SN-theo M:α) 

-- Main theorem

sn-theo : ∀ {Γ M α} → Γ ⊢ M ∶ α → sn M
sn-theo M:α = sound-SN (SN-theo M:α)
