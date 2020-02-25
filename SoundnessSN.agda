module SoundnessSN where

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

infix 5 _↠_ 
infix 5 _→sn_
infix 30 _[_:=_]
infix 30 _[_∣_:=_]
infix 4 _→SN_

_↠_ = _→α*_

_[_:=_] : Λ → V → Λ → Λ
M [ x := N ] =  M ∙ ι ≺+ (x , N)

_[_∣_:=_] : Λ → Σ → V → Λ → Λ
M [ σ ∣ y := P ] = M ∙ σ ≺+ (y , P)

-- Accessibility definition of strongly normalizing terms

data sn : Λ → Set where
  def : ∀ {M} → (∀ {N} → M →β N → sn N) → sn M

data _→sn_ : Λ → Λ → Set where
  β    : ∀ {x M N} → sn N → ƛ x M · N →sn M [ x := N ]
  appl : ∀ {M M' N} → M →sn M' → M · N →sn M' · N
  αsn  : ∀ {M N P} → M →sn N → N ∼α P → M →sn P
--  αsn  : ∀ {M N P} → M ∼α N → M →sn N

-- Convenient definition of strongly normalizing terms

data SN : Λ → Set
data SNe : V → Λ → Set 
data _→SN_ : Λ → Λ → Set

data _→SN_ where
  β    : ∀ {M N x} → SN N → ƛ x M · N →SN M [ x := N ]
  appl : ∀ {M M' N} → M →SN M' → M · N →SN M' · N
  αsn  : ∀ {M N P} → M →SN N → N ∼α P → M →SN P
--  αsn  : ∀ {M N P} → M ∼α N → M →SN N

data SNe where
  v   : ∀ {x} → SNe x (v x)
  app : ∀ {x M N} → SNe x M → SN N → SNe x (M · N)

data SN where
  sne   : ∀ {M x} → SNe x M → SN M 
  abs  : ∀ {M x} → SN M → SN (ƛ x M) 
  exp : ∀ {M N} → M →SN N → SN N → SN M

-- Neutral form

data wne : V → Λ → Set where
  nv   : ∀ {x} → wne x (v x)
  napp : ∀ {x M N} → wne x M → wne x (M · N)

subst-compat₁ : ∀ {M N σ} → M →β N → ∃ λ P → M ∙ σ →β P × P ∼α N ∙ σ

var-irred : ∀ {x M} → (v x) →β M → ⊥ 
var-irred (ctxinj ())

β-equiv : ∀ {M M' N N' x y} → ƛ x M · N ∼α ƛ y M' · N' → M [ x := N ] ∼α M' [ y := N' ]
β-equiv (∼· {N = N} {N' = N'} (∼ƛ {M} {M'} {x} {y} {z} z#ƛxM z#ƛyM' xzM~yzM') N~N') =
  begin
    M [ x := N ]
    ≈⟨ lemma≺+ z#ƛxM ⟩
    M [ x := v z ] [ z := N ]
    ∼⟨ lemma-subst xzM~yzM' (lemma≺+∼α⇂ {z} lemmaι∼α⇂ N~N') ⟩ 
    M' [ y := v z ] [ z := N' ]
    ≈⟨ sym (lemma≺+ z#ƛyM') ⟩
    M' [ y := N' ]
  ∎

lemma-α-ren : ∀ {M N x y} → ƛ x M ∼α ƛ y N → M [ x := v y ] ∼α N
lemma-α-ren (∼ƛ {M}{N}{x}{y}{z} z#ƛxM z#ƛyN M[x=z]~N[y=z]) =
  begin
    M [ x := v y ]
    ≈⟨ lemma≺+ z#ƛxM ⟩
    M [ x := v z ] [ z := v y ]
    ≈⟨ lemmaM∼M'→Mσ≡M'σ M[x=z]~N[y=z] ⟩ 
    N [ y := v z ] [ z := v y ]
    ≈⟨ lemma≺+ι z#ƛyN ⟩ 
    N ∙ ι 
    ∼⟨ ∼σ lemma∙ι ⟩ 
    N
  ∎ 

confl-α : ∀ {M N P} → M ∼α N → M →β P → ∃ λ Q → N →β Q × P ∼α Q
confl-α ∼v (ctxinj ())
confl-α {ƛ x M · N}{ƛ y M' · N'} ƛxMN∼ƛyM'N' (ctxinj ▹β) = M' [ y := N' ] , ctxinj ▹β , β-equiv ƛxMN∼ƛyM'N'
confl-α (∼· ∼v _) (ctxinj ())
confl-α (∼· (∼· _ _) _) (ctxinj ())
confl-α (∼· {_}{_}{_}{N'} M~M' N~N') (ctx·l M→M'') with confl-α M~M' M→M''
... | P , M'→P , M''~P = P · N' , ctx·l M'→P , ∼· M''~P N~N'
confl-α (∼· {_}{M'}{_}{_} M~M' N~N') (ctx·r N→N'') with confl-α N~N' N→N''
... | P , N'→P , N''~P = M' · P , ctx·r N'→P , ∼· M~M' N''~P
confl-α (∼ƛ _ _ _) (ctxinj ())
confl-α {ƛ x M}{ƛ x' M'}{ƛ .x N} (∼ƛ {_}{_}{_}{.x'}{y} y#ƛxM y#ƛx'M' M[y/x]~M'[y/x']) (ctxƛ M→N) = 
  let ƛxM~ƛx'M' = (∼ƛ y#ƛxM y#ƛx'M' M[y/x]~M'[y/x'])
      K₁ , M[x'/x]→K₁ , K₁∼N[x'/x] = subst-compat₁ {σ = ι ≺+ (x , v x')} M→N
      M[x'/x]~M' = lemma-α-ren ƛxM~ƛx'M'
      K₂ , M'→K₂ , K₁∼K₂ = confl-α M[x'/x]~M' M[x'/x]→K₁
      ƛx'M'→ƛx'K₂ = ctxƛ {x = x'} M'→K₂
      x'#ƛxN = lemma→β# (lemmaM∼N# (∼σ ƛxM~ƛx'M') x' #ƛ≡) (ctxƛ M→N)
      ƛx'K₂∼ƛxN = ∼τ (lemma∼λ {x = x'} (∼τ (∼σ K₁∼K₂) K₁∼N[x'/x])) (∼σ (corollary4-2' x'#ƛxN))
  in ƛ x' K₂ , ƛx'M'→ƛx'K₂ , ∼σ ƛx'K₂∼ƛxN

confl-α* : ∀ {M N P} → M ∼α N → M ↠ P → ∃ λ Q → N ↠ Q × P ∼α Q
confl-α* {M} {N} {.M} M∼N refl = N , refl , M∼N
confl-α* M∼N (just (inj₁ M→P)) =
  let Q , N→Q , P∼Q = confl-α M∼N M→P
  in Q , just (inj₁ N→Q) , P∼Q
confl-α* {M} M∼N (just (inj₂ M∼P)) = M , just (inj₂ (∼σ M∼N)) , ∼σ M∼P
confl-α* M∼N (trans M→P P→Q) =
  let R , N→R , P∼R = confl-α* M∼N M→P
      S , R→S , Q∼S = confl-α* P∼R P→Q
  in S , trans N→R R→S , Q∼S

sn-α : ∀ {M N} → M ∼α N → sn M → sn N
sn-α {_}{N} M~N (def hi) = def λ N→P → sn-α-aux N→P
  where sn-α-aux : ∀ {P} → N →β P → sn P
        sn-α-aux N→P with confl-α (∼σ M~N) N→P
        ... | _ , M→Q , P~Q = sn-α (∼σ P~Q) (hi M→Q)

⟶²⇒⟶* : ∀ {M N P} → M →β N × N ∼α P → M ↠ P
⟶²⇒⟶* (M→P , P~N) = trans (just (inj₁ M→P)) (just (inj₂ P~N))

#⇂-preservedby-β : ∀ {M M' z σ} → M →β M' → z #⇂ (σ , M) → z #⇂ (σ , M')
#⇂-preservedby-β M→M' z#σM = λ x x*M → z#σM x (lemma→α* x*M M→M')

lemma∼α∙ : ∀ {M σ y z N} → z #⇂ (σ , ƛ y M) → M [ σ ∣ y := v z ] [ z := N ∙ σ ] ∼α M [ y := N ] ∙ σ
lemma∼α∙ {M} {σ} {y} {z} {N} z#σ =
  begin
    M [ σ ∣ y :=  v z ] [ z := N ∙ σ ]
    ∼⟨ corollary1SubstLemma z#σ ⟩
    M [ σ ∣ y := N ∙ σ ]
    ≈⟨ corollary1Prop7 {M}{N}{σ}{y} ⟩
    M [ y := N ] ∙ σ
  ∎

-- Lemma 5

--subst-compat₁ : ∀ {M N σ} → M ⟶ N → M ∙ σ ⟶² N ∙ σ 
subst-compat₁ {ƛ y M · N}{_}{σ} (ctxinj ▹β) = M [ σ ∣ y := v z ] [ z := N ∙ σ ] , ctxinj ▹β , lemma∼α∙ z#σ
  where z = χ (σ , ƛ y M)
        z#σ = χ-lemma2 σ (ƛ y M)
subst-compat₁ {v _ · _} (ctxinj ())
subst-compat₁ {(_ · _) · _} (ctxinj ())
subst-compat₁ {v _} (ctxinj ())
subst-compat₁ {ƛ _ _} (ctxinj ())
subst-compat₁ {_ · N}{_}{σ} (ctx·l M→M') =
  let Q , Mσ→Q , Q~M'σ = subst-compat₁ M→M'
  in Q · (N ∙ σ) , ctx·l Mσ→Q , ∼· Q~M'σ ∼ρ
subst-compat₁ {M · _}{_}{σ} (ctx·r N→N') =
  let Q , Nσ→Q , Q~N'σ = subst-compat₁ N→N'
  in (M ∙ σ) · Q , ctx·r Nσ→Q , ∼· ∼ρ Q~N'σ
subst-compat₁ {ƛ x M}{ƛ .x M'}{σ} (ctxƛ M→M') =
  let z = χ (σ , ƛ x M)
      z#σ = χ-lemma2 σ (ƛ x M)
      N , Mσ,z/x→N , N~M'σ,z/x = subst-compat₁ {M}{M'} M→M'
      aux = begin
              ƛ z N
              ∼⟨ lemma∼λ N~M'σ,z/x ⟩
              ƛ z (M' [ σ ∣ x := v z ])
              ∼⟨ ∼σ (corollary4-2 (#⇂-preservedby-β (ctxƛ M→M') z#σ)) ⟩
              ƛ x M' ∙ σ
            ∎
  in ƛ z N , ctxƛ Mσ,z/x→N , aux

-- Lemma 6

subst-compat₂ : ∀ {N N'} → (x : V) → (M : Λ) → N →β N' → M [ x := N ] ↠ M [ x := N' ]
subst-compat₂ x M N→N' = lemma⇉⊆→α* (lemma⇉ (⇉ρ {M}) (corollary⇉ₛ≺+ x (lemma→α⊆⇉ (inj₁ N→N'))))

-- Lemma 8

multistep : ∀ {M M'} → M ↠ M' → sn M → sn M'
multistep refl snM = snM
multistep (just (inj₁ M→M')) (def snM) = snM M→M'
multistep (just (inj₂ M~M')) snM = sn-α M~M' snM
multistep (trans M→*N N→*P) snM = multistep N→*P (multistep M→*N snM)

-- Lemma 9

lemma-sn-v : ∀ {x} → sn (v x)
lemma-sn-v = def λ x→M → ⊥-elim (var-irred x→M) 

lemma-sn-ƛ : ∀ {x M} → sn M → sn (ƛ x M)
lemma-sn-ƛ snM = def λ ƛxM→P → lemma-sn-ƛ-aux snM ƛxM→P 
  where lemma-sn-ƛ-aux : ∀ {x M P} → sn M → ƛ x M →β P → sn P
        lemma-sn-ƛ-aux _ (ctxinj ())
        lemma-sn-ƛ-aux (def M→Q⇒snQ) (ctxƛ M→M') = lemma-sn-ƛ (M→Q⇒snQ M→M')
  
inv-app-lemma : ∀ {M N} → sn (M · N) → sn M × sn N
inv-app-lemma snMN = (def λ M→P → lemma-sn-app-aux₁ snMN M→P) , (def λ N→P → lemma-sn-app-aux₂ snMN N→P)
  where lemma-sn-app-aux₁ : ∀ {M N P} → sn (M · N) → M →β P → sn P
        lemma-sn-app-aux₁ (def MN→P⇒snP) M→P = proj₁ (inv-app-lemma (MN→P⇒snP (ctx·l M→P)))
        lemma-sn-app-aux₂ : ∀ {M N P} → sn (M · N) → N →β P → sn P
        lemma-sn-app-aux₂ (def MN→P⇒snP) N→P = proj₂ (inv-app-lemma (MN→P⇒snP (ctx·r N→P)))

-- Lemma 10 (Weak head expansion)

wkh-exp-α : ∀ {M N x Q} → sn N → sn Q → Q ∼α M [ x := N ] → sn (ƛ x M · N)

wkh-exp-α-aux : ∀ {M x N P Q} → sn N → sn Q → Q ∼α M [ x := N ] → ƛ x M · N →β P → sn P
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

-- Lemma 11

closure→Ne : ∀ {R R' x} → wne x R → R →β R' → wne x R'
closure→Ne nv (ctxinj ())
closure→Ne (napp ()) (ctxinj ▹β)
closure→Ne (napp R∈ne) (ctx·l R→P) = napp (closure→Ne R∈ne R→P)
closure→Ne (napp R∈ne) (ctx·r {_}{_}{P} N→P) = napp R∈ne

closure·Ne : ∀ {R N x} → wne x R → sn R → sn N → sn (R · N)

closure·Ne-aux : ∀ {R N Q x} → wne x R → sn R → sn N → R · N →β Q → sn Q
closure·Ne-aux () snR snN (ctxinj ▹β)
closure·Ne-aux neR (def R→P⇒snP) snN (ctx·l R→R') = closure·Ne (closure→Ne neR R→R') (R→P⇒snP R→R') snN
closure·Ne-aux neR snR (def N→P⇒snP) (ctx·r N→N') = closure·Ne neR snR (N→P⇒snP N→N')

-- closure·Ne : ∀ {R N} → ne R → sn R → sn N → sn (R · N)
closure·Ne R∈ne R∈sn N∈sn = def λ RN→Q → closure·Ne-aux R∈ne R∈sn N∈sn RN→Q

-- Lemma 12 (Confluence)

abs-snred-ƛ : ∀ {x M P} → ƛ x M →sn P → ⊥
abs-snred-ƛ (αsn ƛxM→P _) = abs-snred-ƛ ƛxM→P

confluence : ∀ {M N N'} → M →sn N → M →β N' → N ∼α N' ⊎ ∃ (λ Q → N' →sn Q × N ↠ Q)
confluence (β _) (ctxinj ▹β) = inj₁ ∼ρ
confluence {ƛ x M · N} (β N∈sn) (ctx·l (ctxƛ {._}{._}{M'} M→M')) = inj₂ (M' [ x := N ] , β N∈sn , ⟶²⇒⟶* (proj₂ (subst-compat₁ M→M')))
confluence (β _) (ctx·l (ctxinj ()))
confluence {ƛ x M · N} (β (def N→N'⇒N∈sn)) (ctx·r .{_}{._}{N'} N→N') = inj₂ (M [ x := N' ] , β (N→N'⇒N∈sn N→N') , subst-compat₂ x M N→N')
confluence (appl (αsn λxM→P _)) (ctxinj ▹β) = ⊥-elim (abs-snred-ƛ λxM→P)
confluence (appl (appl _)) (ctxinj ())
confluence (appl (β _)) (ctxinj ())
confluence {M · N} (appl M→snM') (ctx·l M→M₂) with confluence M→snM' M→M₂
... | inj₁ M'∼M₂ = inj₁ (∼· M'∼M₂ ∼ρ)
... | inj₂ (P , M₂→snP , M'→*P) = inj₂ (P · N , appl M₂→snP , app-star-l M'→*P)
confluence {M · N}{M' · .N}{.M · N'} (appl M→snM') (ctx·r N→N') = inj₂ (M' · N' , appl M→snM' , just (app-step-r (inj₁ N→N')))
confluence (αsn M→N N∼P) M→Q with confluence M→N M→Q
... | inj₁ N∼Q = inj₁ (∼τ (∼σ N∼P) N∼Q)
... | inj₂ (S , Q→S , N→*S) = 
  let T , P→*T , S∼T = confl-α* N∼P N→*S
  in inj₂ (T , (αsn Q→S S∼T) , P→*T)

-- Lemma 13

backward→sn-aux : ∀ {M N M'} → sn M → sn N → M →sn M' → sn (M' · N) → sn (M · N)

backward→sn-aux' : ∀ {M N M' Q} → M · N →β Q → sn M → sn N → M →sn M' → sn (M' · N) → sn Q
backward→sn-aux' (ctxinj ▹β) _ _ (αsn λxM→P _) _ = ⊥-elim (abs-snred-ƛ λxM→P)
backward→sn-aux' {.M} {.N} (ctx·l {M} {M''} {N} M→M'') (def M→Q⇒Q∈sn) N∈sn M→snM' M'N∈sn with confluence M→snM' M→M''
... | inj₁ M'∼M'' = sn-α (∼· M'∼M'' ∼ρ) M'N∈sn
... | inj₂ (P , M''→snP , M'→*P) = backward→sn-aux (M→Q⇒Q∈sn M→M'') N∈sn M''→snP (multistep (app-star-l M'→*P) M'N∈sn )
backward→sn-aux' {_}{N}{M'} (ctx·r {_}{_}{N'} N→N') M∈sn (def N→Q⇒Q∈sn) M→snM' (def M'N→Q⇒Q∈sn) =
  backward→sn-aux M∈sn (N→Q⇒Q∈sn N→N') M→snM' (M'N→Q⇒Q∈sn (ctx·r N→N'))

-- backward→sn-aux : ∀ {M N M'} → sn M → sn N → M →sn M' → sn (M' · N) → sn (M · N)
backward→sn-aux M∈sn N∈Sn M→snM' M'N∈sn = def λ MN→Q → backward→sn-aux' MN→Q M∈sn N∈Sn M→snM' M'N∈sn

backward→sn : ∀ {M M'} → M →sn M' → sn M' → sn M
backward→sn (αsn M→N N∼P) P∈sn = backward→sn M→N (sn-α (∼σ N∼P) P∈sn) 
backward→sn (β N∈sn) M[x=N]∈sn = wkh-exp N∈sn M[x=N]∈sn
backward→sn {M · N} {M' · .N} (appl M→M') M'N∈sn = let snM' , snN = inv-app-lemma M'N∈sn
                                                   in backward→sn-aux (backward→sn M→M' snM') snN M→M' M'N∈sn
-- Lemma 14

lemma-ne : ∀ {M x} → SNe x M → wne x M
lemma-ne v = nv
lemma-ne (app M∈ne _) = napp (lemma-ne M∈ne)

-- Theorem 1

sound-SN  : ∀ {M} → SN M → sn M

sound-SNe : ∀ {M x} → SNe x M → sn M

sound→SN  : ∀ {M N} → M →SN N → M →sn N

-- sound-SN : ∀ {M} → SN M → sn M
sound-SN (sne x) = sound-SNe x
sound-SN (abs x) = lemma-sn-ƛ (sound-SN x)
sound-SN (exp M→N N∈Sn) = backward→sn (sound→SN M→N) (sound-SN N∈Sn)

-- sound-SNe : ∀ {M} → SNe M → sn M
sound-SNe v = lemma-sn-v
sound-SNe (app M∈SNe N∈Sn) = closure·Ne (lemma-ne M∈SNe) (sound-SNe M∈SNe) (sound-SN N∈Sn)

-- sound→SN : ∀ {M N} → M →SN N → M →sn N
sound→SN (αsn M→N N∼P) = αsn (sound→SN M→N) N∼P
sound→SN (β M∈Sn) = β (sound-SN M∈Sn)
sound→SN (appl M→M') = appl (sound→SN M→M')
