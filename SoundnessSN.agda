module SoundnessSN where

-- Sebastián Urciuoli
-- s.urciuoli@gmail.com
-- 2019

-- This file contains a solution for the challenge number one of the POPLMark benchmark
-- described at: http://www.cse.chalmers.se/~abela/poplmark2.pdf
-- In this solution we use Stoughton's multiple substitution framework: http://ernius.github.io/formalmetatheory-stoughton

open import Chi
open import Term renaming (_⟶_ to _⇒_) hiding (_∶_)
open import Beta
open import Substitution hiding (_∘_)
open import Alpha
open import Relation Λ 
open import ParallelReduction
open import SubstitutionLemmas

open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Relation.Binary.Core hiding (Rel)
open import Data.Product hiding (Σ)
open import Data.Nat hiding (_≟_)
open import Function
open import Relation.Binary.PropositionalEquality using (sym; subst₂)

infix 4 _⟶_
infix 4 _⟶²_
infix 5 _⟶*_
infix 5 _→sn_
infix 30 _[_:=_]
infix 30 _[_∣_:=_]
infix 4 _→SN_,_

_⟶_ : Λ → Λ → Set
M ⟶ N = M →β N

_⟶*_ : Λ → Λ → Set
M ⟶* N = M →α* N

_⟶²_ : Λ → Λ → Set
M ⟶² N = ∃ λ P → M →β P × P ∼α N

_[_:=_] : Λ → V → Λ → Λ
M [ x := N ] =  M ∙ ι ≺+ (x , N)

_[_∣_:=_] : Λ → Σ → V → Λ → Λ
M [ σ ∣ y := P ] = M ∙ σ ≺+ (y , P)

-- Accesibility definition for strong normalizing terms

data sn : Λ → Set where
  def : ∀ {M} → (∀ {N} → M ⟶ N → sn N) → sn M

data _→sn_ : Λ → Λ → Set where
  β    : ∀ {x M N} → sn N → ƛ x M · N →sn M [ x := N ]
  appl : ∀ {M M' N} → M →sn M' → M · N →sn M' · N

-- Inductive definition for strong normalizing terms

data SN : ℕ → Λ → Set
data SNe : ℕ → Λ → Set 
data _→SN_,_ : Λ → ℕ → Λ → Set

data _→SN_,_ where
  β    : ∀ {M N x n} → SN n N → ƛ x M · N →SN (suc n) , M [ x := N ]
  appl : ∀ {M M' N n} → M →SN n , M' → M · N →SN (suc n) , M' · N   

data SNe where
  v   : ∀ {x} → SNe 0 (v x)
  app : ∀ {M N m n} → SNe m M → SN n N → SNe (suc (m ⊔ n)) (M · N)

data SN where
  sne   : ∀ {M m} → SNe m M → SN (suc m) M 
  abs  : ∀ {M x m} → SN m M → SN (suc m) (ƛ x M) 
  exp : ∀ {M N m n} → M →SN m , N → SN n N → SN (suc (m ⊔ n)) M

-- Neutral form

data ne : Λ → Set where
  nv   : ∀ {x} → ne (v x)
  napp : ∀ {M N} → ne M → ne (M · N)

-- start of auxiliary lemmas (overhead) --

subst-compat₁ : ∀ {M N σ} → M ⟶ N → M ∙ σ ⟶² N ∙ σ

var-irred : ∀ {x M} → (v x) ⟶ M → ⊥ 
var-irred (ctxinj ())

≡→α : ∀ {M N} -> M ≡ N -> M ∼α N
≡→α {M} M≡N = subst₂ _∼α_ refl M≡N (∼ρ {M})

confl-α : ∀ {M N P} → M ∼α N → M ⟶ P → ∃ λ Q → N ⟶ Q × P ∼α Q
confl-α ∼v (ctxinj ())
confl-α {ƛ x M · N}{ƛ y M' · N'} (∼· (∼ƛ {.M}{.M'}{.x}{.y}{z} z#ƛxM z#ƛyM' xzM~yzM') N~N') (ctxinj ▹β) = M' [ y := N' ] , ctxinj ▹β , aux
  where aux = begin
                M [ x := N ]
                ≈⟨ lemma≺+ z#ƛxM ⟩
                M [ x := v z ] [ z := N ]
                ∼⟨ lemma-subst xzM~yzM' (lemma≺+∼α⇂ {z} lemmaι∼α⇂ N~N') ⟩ 
                M' [ y := v z ] [ z := N' ]
                ≈⟨ sym (lemma≺+ z#ƛyM') ⟩
                M' [ y := N' ]
              ∎ 
confl-α (∼· ∼v _) (ctxinj ())
confl-α (∼· (∼· _ _) _) (ctxinj ())
confl-α (∼· {_}{_}{_}{N'} M~M' N~N') (ctx·l M→M'') with confl-α M~M' M→M''
... | P , M'→P , M''~P = P · N' , ctx·l M'→P , ∼· M''~P N~N'
confl-α (∼· {_}{M'}{_}{_} M~M' N~N') (ctx·r N→N'') with confl-α N~N' N→N''
... | P , N'→P , N''~P = M' · P , ctx·r N'→P , ∼· M~M' N''~P
confl-α (∼ƛ _ _ _) (ctxinj ())
confl-α {ƛ x M}{ƛ x' M'}{ƛ .x N} (∼ƛ {_}{_}{_}{.x'}{y} y#ƛxM y#ƛx'M' M[y/x]~M'[y/x']) (ctxƛ M→N) = 
  let K₁ , M[x'/x]→K₁ , K₁∼N[x'/x] = subst-compat₁ {σ = ι ≺+ (x , v x')} M→N
      M[x'/x]~M' = subst₂ _∼α_ (sym (lemma≺+ y#ƛxM)) refl (∼τ (∼τ (≡→α (lemmaM∼M'→Mσ≡M'σ {σ = (ι ≺+ (y , v x'))} M[y/x]~M'[y/x'])) (≡→α (lemma≺+ι y#ƛx'M'))) (∼σ lemma∙ι))
      K₂ , M'→K₂ , K₁∼K₂ = confl-α M[x'/x]~M' M[x'/x]→K₁
      ƛx'M'→ƛx'K₂ = ctxƛ {x = x'} M'→K₂
      x'#ƛxN = lemma→β# (lemmaM∼N# (∼σ (∼ƛ y#ƛxM y#ƛx'M' M[y/x]~M'[y/x'])) x' #ƛ≡) (ctxƛ M→N)
      ƛx'K₂∼ƛxN = ∼τ (lemma∼λ {x = x'} (∼τ (∼σ K₁∼K₂) K₁∼N[x'/x])) (∼σ (corollary4-2' x'#ƛxN))
  in ƛ x' K₂ , ƛx'M'→ƛx'K₂ , ∼σ ƛx'K₂∼ƛxN

sn-α : ∀ {M N} → M ∼α N → sn M → sn N
sn-α {_}{N} M~N (def hi) = def λ N→P → sn-α-aux N→P
  where sn-α-aux : ∀ {P} → N ⟶ P → sn P
        sn-α-aux N→P with confl-α (∼σ M~N) N→P
        ... | _ , M→Q , P~Q = sn-α (∼σ P~Q) (hi M→Q)

⟶²⇒⟶* : ∀ {M N} → M ⟶² N → M ⟶* N
⟶²⇒⟶* (_ , M→P , P~N) = trans (just (inj₁ M→P)) (just (inj₂ P~N))

#⇂-preservedby-β : ∀ {M M' z σ} → M ⟶ M' → z #⇂ (σ , M) → z #⇂ (σ , M')
#⇂-preservedby-β M→M' z#σM = λ x x*M → z#σM x (lemma→α* x*M M→M')

lemma∼α∙ : ∀ {M σ y z N} → z #⇂ (σ , ƛ y M) → M [ σ ∣ y := v z ] [ z := N ∙ σ ] ∼α M [ y := N ] ∙ σ
lemma∼α∙ {M} {σ} {y} {z} {N} z#σ =
  begin
    M [ σ ∣ y := v z ] [ z := N ∙ σ ]
    ∼⟨ corollary1SubstLemma z#σ ⟩
    M [ σ ∣ y := N ∙ σ ]
    ≈⟨ corollary1Prop7 {M}{N}{σ}{y} ⟩
    M [ y := N ] ∙ σ
  ∎
              
-- end of auxiliary lemmas (overhead) --

-- Lemma 5

--subst-compat₁ : ∀ {M N σ} → M ⟶ N → M ∙ σ ⟶² N ∙ σ 
subst-compat₁ {ƛ y M · N}{_}{σ} (ctxinj ▹β) = M [ σ ∣ y := v z ] [ z := N ∙ σ ] , ctxinj ▹β , lemma∼α∙ z#σ
  where z = χ (σ , ƛ y M)
        z#σ = χ-lemma2 σ (ƛ y M)
subst-compat₁ {v _ · _} (ctxinj ())
subst-compat₁ {(_ · _) · _} (ctxinj ())
subst-compat₁ {v _} (ctxinj ())
subst-compat₁ {ƛ _ _} (ctxinj ())
subst-compat₁ {_ · N}{_}{σ} (ctx·l M→M') = let Q , Mσ→Q , Q~M'σ = subst-compat₁ M→M' in Q · (N ∙ σ) , ctx·l Mσ→Q , ∼· Q~M'σ ∼ρ
subst-compat₁ {M · _}{_}{σ} (ctx·r N→N') = let Q , Nσ→Q , Q~N'σ = subst-compat₁ N→N' in (M ∙ σ) · Q , ctx·r Nσ→Q , ∼· ∼ρ Q~N'σ
subst-compat₁ {ƛ x M}{ƛ .x M'}{σ} (ctxƛ M→M') = let z = χ (σ , ƛ x M)
                                                    z#σ = χ-lemma2 σ (ƛ x M)
                                                    N , Mσ,z/x→N , N~M'σ,z/x = subst-compat₁ {M}{M'} M→M'
                                                    aux = begin
                                                            ƛ z N
                                                            ∼⟨ lemma∼λ N~M'σ,z/x ⟩
                                                            ƛ z (M' [ σ ∣ x := v z ] )
                                                            ∼⟨ ∼σ (corollary4-2 (#⇂-preservedby-β (ctxƛ M→M') z#σ)) ⟩
                                                            ƛ x M' ∙ σ
                                                          ∎
                                                in ƛ z N , ctxƛ Mσ,z/x→N , aux

-- Lemma 6

subst-compat₂ : ∀ {N N'} → (x : V) → (M : Λ) → N ⟶ N' → M [ x := N ] ⟶* M [ x := N' ]
subst-compat₂ x M N→N' = lemma⇉⊆→α* (lemma⇉ (⇉ρ {M}) (corollary⇉ₛ≺+ x (lemma→α⊆⇉ (inj₁ N→N'))))

-- Lemma 8

multistep : ∀ {M M'} → M ⟶* M' → sn M → sn M'
multistep refl snM = snM
multistep (just (inj₁ M→M')) (def snM) = snM M→M'
multistep (just (inj₂ M~M')) snM = sn-α M~M' snM
multistep (trans M→*N N→*P) snM = multistep N→*P (multistep M→*N snM)

-- Lemma 9

lemma-sn-v : ∀ {x} → sn (v x)
lemma-sn-v = def λ x→M → ⊥-elim (var-irred x→M) 

lemma-sn-ƛ : ∀ {x M} → sn M → sn (ƛ x M)
lemma-sn-ƛ snM = def λ ƛxM→P → lemma-sn-ƛ-aux snM ƛxM→P 
  where lemma-sn-ƛ-aux : ∀ {x M P} → sn M → ƛ x M ⟶ P → sn P
        lemma-sn-ƛ-aux _ (ctxinj ())
        lemma-sn-ƛ-aux (def M→Q⇒snQ) (ctxƛ M→M') = lemma-sn-ƛ (M→Q⇒snQ M→M')
  
inv-app-lemma : ∀ {M N} → sn (M · N) → sn M × sn N
inv-app-lemma snMN = (def λ M→P → lemma-sn-app-aux₁ snMN M→P) , (def λ N→P → lemma-sn-app-aux₂ snMN N→P)
  where lemma-sn-app-aux₁ : ∀ {M N P} → sn (M · N) → M ⟶ P → sn P
        lemma-sn-app-aux₁ (def MN→P⇒snP) M→P = proj₁ (inv-app-lemma (MN→P⇒snP (ctx·l M→P)))
        lemma-sn-app-aux₂ : ∀ {M N P} → sn (M · N) → N ⟶ P → sn P
        lemma-sn-app-aux₂ (def MN→P⇒snP) N→P = proj₂ (inv-app-lemma (MN→P⇒snP (ctx·r N→P)))

-- Lemma 10 (Weak head expansion)

-- this section has substantial differences --

wkh-exp-α : ∀ {M N x Q} → sn N → sn Q → Q ∼α M [ x := N ] → sn (ƛ x M · N)

wkh-exp-α-aux : ∀ {M x N P Q} → sn N → sn Q → Q ∼α M [ x := N ] → ƛ x M · N ⟶ P → sn P
wkh-exp-α-aux snN snQ Q~M[N/x] (ctxinj ▹β) = sn-α Q~M[N/x] snQ
wkh-exp-α-aux _ _ _ (ctx·l (ctxinj ()))
wkh-exp-α-aux {_}{x} snN (def hi) Q~M[N/x] (ctx·l (ctxƛ M→M')) =
  let _ , M[N/x]→R , R~M'[N/x] = subst-compat₁ M→M'
      _ , Q→S , R~S  = confl-α (∼σ Q~M[N/x]) M[N/x]→R
  in wkh-exp-α snN (hi Q→S) (∼τ (∼σ R~S) R~M'[N/x])
wkh-exp-α-aux {M}{x} (def hi) snQ Q~M[N/x] (ctx·r N→N') = wkh-exp-α (hi N→N') (multistep (subst-compat₂ x M N→N') (sn-α Q~M[N/x] snQ)) ∼ρ

wkh-exp-α snN snQ Q~M[N/x] = def λ ƛxMN→Q → wkh-exp-α-aux snN snQ Q~M[N/x] ƛxMN→Q

wkh-exp : ∀ {M N x} → sn N → sn (M [ x := N ]) → sn (ƛ x M · N)
wkh-exp snN snM[N/x] = wkh-exp-α snN snM[N/x] ∼ρ

-- end of secion --

-- Lemma 11

closure→Ne : ∀ {R R'} → ne R → R ⟶ R' → ne R'
closure→Ne nv (ctxinj ())
closure→Ne (napp ()) (ctxinj ▹β)
closure→Ne (napp R∈ne) (ctx·l R→P) = napp (closure→Ne R∈ne R→P)
closure→Ne (napp R∈ne) (ctx·r {_}{_}{P} N→P) = napp R∈ne

closure·Ne : ∀ {R N} → ne R → sn R → sn N → sn (R · N)

closure·Ne-aux : ∀ {R N Q} → ne R → sn R → sn N → R · N ⟶ Q → sn Q
closure·Ne-aux () snR snN (ctxinj ▹β)
closure·Ne-aux neR (def R→P⇒snP) snN (ctx·l R→R') = closure·Ne (closure→Ne neR R→R') (R→P⇒snP R→R') snN
closure·Ne-aux neR snR (def N→P⇒snP) (ctx·r N→N') = closure·Ne neR snR (N→P⇒snP N→N')

-- closure·Ne : ∀ {R N} → ne R → sn R → sn N → sn (R · N)
closure·Ne R∈ne R∈sn N∈sn = def λ RN→Q → closure·Ne-aux R∈ne R∈sn N∈sn RN→Q

-- Lemma 12 (Confluence)

confluence : ∀ {M N N'} → M →sn N → M ⟶ N' → N ≡ N' ⊎ ∃ (λ Q → N' →sn Q × N ⟶* Q)
confluence (β _) (ctxinj ▹β) = inj₁ refl
confluence {ƛ x M · N} (β N∈sn) (ctx·l (ctxƛ {._}{._}{M'} M→M')) = inj₂ (M' [ x := N ] , β N∈sn , ⟶²⇒⟶* (subst-compat₁ M→M'))
confluence (β _) (ctx·l (ctxinj ()))
confluence {ƛ x M · N} (β (def N→N'⇒N∈sn)) (ctx·r .{_}{._}{N'} N→N') = inj₂ (M [ x := N' ] , β (N→N'⇒N∈sn N→N') , subst-compat₂ x M N→N')
confluence (appl ()) (ctxinj ▹β)
confluence {M · N} (appl M→snM') (ctx·l M→M₂) with confluence M→snM' M→M₂
... | inj₁ refl = inj₁ refl
... | inj₂ (P , M₂→snP , M'→*P) = inj₂ (P · N , appl M₂→snP , app-star-l M'→*P)
confluence {M · N}{M' · .N}{.M · N'} (appl M→snM') (ctx·r N→N') = inj₂ (M' · N' , appl M→snM' , just (app-step-r (inj₁ N→N')))

-- Lemma 13

backward→sn-aux : ∀ {M N M'} → sn M → sn N → M →sn M' → sn (M' · N) → sn (M · N)

backward→sn-aux' : ∀ {M N M' Q} → M · N ⟶ Q → sn M → sn N → M →sn M' → sn (M' · N) → sn Q
backward→sn-aux' (ctxinj ▹β) _ _ () _
backward→sn-aux' {.M} {.N} (ctx·l {M} {M''} {N} M→M'') (def M→Q⇒Q∈sn) N∈sn M→snM' M'N∈sn with confluence M→snM' M→M''
... | inj₁ refl = M'N∈sn
... | inj₂ (P , M''→snP , M'→*P) = backward→sn-aux (M→Q⇒Q∈sn M→M'') N∈sn M''→snP (multistep (app-star-l M'→*P) M'N∈sn )
backward→sn-aux' {_}{N}{M'} (ctx·r {_}{_}{N'} N→N') M∈sn (def N→Q⇒Q∈sn) M→snM' (def M'N→Q⇒Q∈sn) =
  backward→sn-aux M∈sn (N→Q⇒Q∈sn N→N') M→snM' (M'N→Q⇒Q∈sn (ctx·r N→N'))

-- backward→sn-aux : ∀ {M N M'} → sn M → sn N → M →sn M' → sn (M' · N) → sn (M · N)
backward→sn-aux M∈sn N∈Sn M→snM' M'N∈sn = def λ MN→Q → backward→sn-aux' MN→Q M∈sn N∈Sn M→snM' M'N∈sn

backward→sn : ∀ {M M'} → M →sn M' → sn M' → sn M
backward→sn (β N∈sn) M[x=N]∈sn = wkh-exp N∈sn M[x=N]∈sn
backward→sn {M · N} {M' · .N} (appl M→M') M'N∈sn = let snM' , snN = inv-app-lemma M'N∈sn
                                                   in backward→sn-aux (backward→sn M→M' snM') snN M→M' M'N∈sn
-- Lemma 14

lemma-ne : ∀ {M n} → SNe n M → ne M
lemma-ne v = nv
lemma-ne (app M∈ne _) = napp (lemma-ne M∈ne)

-- Theorem 1

sound-SN  : ∀ {M n} → SN n M → sn M

sound-SNe : ∀ {M n} → SNe n M → sn M

sound→SN  : ∀ {M N n} → M →SN n , N → M →sn N

-- sound-SN : ∀ {M} → SN M → sn M
sound-SN (sne x) = sound-SNe x
sound-SN (abs x) = lemma-sn-ƛ (sound-SN x)
sound-SN (exp M→N N∈Sn) = backward→sn (sound→SN M→N) (sound-SN N∈Sn)

-- sound-SNe : ∀ {M} → SNe M → sn M
sound-SNe v = lemma-sn-v
sound-SNe (app M∈SNe N∈Sn) = closure·Ne (lemma-ne M∈SNe) (sound-SNe M∈SNe) (sound-SN N∈Sn)

-- sound→SN : ∀ {M N} → M →SN N → M →sn N
sound→SN (β M∈Sn) = β (sound-SN M∈Sn)
sound→SN (appl M→M') = appl (sound→SN M→M')