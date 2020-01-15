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
open import Data.Product
open import Data.Nat hiding (_≟_)
open import Function

infix 4 _⟶_
infix 4 _⟶²_
infix 5 _⟶*_
infix 5 _→sn_
infix 30 _[_:=_]
infix 30 _[_:=_,_:=_]
infix 5 _→SN_

_⟶_ : Λ → Λ → Set
M ⟶ N = M →β N

_⟶*_ : Λ → Λ → Set
M ⟶* N = M →α* N

_⟶²_ : Λ → Λ → Set
M ⟶² N = ∃ λ P → M →β P × P ∼α N

_[_:=_] : Λ → V → Λ → Λ
M [ x := N ] =  M ∙ ι ≺+ (x , N)

_[_:=_,_:=_] : Λ → V → Λ → V → Λ → Λ
M [ x := N , y := P ] = M ∙ ι ≺+ (x , N) ≺+ (y , P)

-- Accesibility definition for strong normalizing terms

data sn : Λ → Set where
  def : ∀ {M} → (∀ {N} → M ⟶ N → sn N) → sn M

data _→sn_ : Λ → Λ → Set where
  β    : ∀ {x M N} → sn N → ƛ x M · N →sn M [ x := N ]
  appl : ∀ {M M' N} → M →sn M' → M · N →sn M' · N

-- Inductive definition for strong normalizing terms

data SN : Λ → Set
data SNe : Λ → Set 
data _→SN_ : Λ → Λ → Set

data _→SN_ where
  β    : ∀ {M N x} → SN N → ƛ x M · N →SN M [ x := N ]
  appl : ∀ {M M' N} → M →SN M' → M · N →SN M' · N   

data SNe where
  v   : (x : V) → SNe (v x)
  app : ∀ {M N} → SNe M → SN N → SNe (M · N)

data SN where
  sne   : ∀ {M} → SNe M → SN M 
  abs  : ∀ {M x} → SN M → SN (ƛ x M) 
  step : ∀ {M N} → M →SN N → SN N → SN M

-- Neutral form

data ne : Λ → Set where
  nev : (x : V) → ne (v x)
  ne· : ∀ {r} → ne r → (s : Λ) → ne (r · s)

-- start of auxiliary lemmas (overhead) --

var-irred : ∀ {x M} → (v x) ⟶ M → ⊥ 
var-irred (ctxinj ())

confl-α : ∀ {M N P} → M ∼α N → M ⟶ P → ∃ λ Q → N ⟶ Q × P ∼α Q
confl-α ∼v (ctxinj ())
confl-α {_}{ƛ y M' · N'} (∼· (∼ƛ z#ƛxM z#ƛyM' xzM~yzM') N~N') (ctxinj ▹β) = M' [ y := N' ] , ctxinj ▹β , {!!} 
confl-α (∼· ∼v _) (ctxinj ())
confl-α (∼· (∼· _ _) _) (ctxinj ())
confl-α (∼· {_}{_}{_}{N'} M~M' N~N') (ctx·l M→M'') with confl-α M~M' M→M''
... | P , M'→P , M''~P = P · N' , ctx·l M'→P , ∼· M''~P N~N'
confl-α (∼· {_}{M'}{_}{_} M~M' N~N') (ctx·r N→N'') with confl-α N~N' N→N''
... | P , N'→P , N''~P = M' · P , ctx·r N'→P , ∼· M~M' N''~P
confl-α (∼ƛ _ _ _) (ctxinj ())
confl-α (∼ƛ x₁ x₂ xzM~yzM') (ctxƛ M→M'') = {!!}

sn-α : ∀ {M N} → M ∼α N → sn M → sn N
sn-α {_}{N} M~N (def hi) = def λ N→P → sn-α-aux N→P
  where sn-α-aux : ∀ {P} → N ⟶ P → sn P
        sn-α-aux N→P with confl-α {!!} N→P
        ... | _ , M→N , N~N' = {!!} -- sn-α N~N' (hi M→N)

⟶²⇒⟶* : ∀ {M N} → M ⟶² N → M ⟶* N
⟶²⇒⟶* (_ , M→P , P~N) = trans (just (inj₁ M→P)) (just (inj₂ P~N))

-- end of auxiliary lemmas (overhead) --

-- Lemma 5

subst-compat₁ : ∀ {M N x P} → M ⟶ N → M [ x := P ] ⟶² N [ x := P ]
subst-compat₁ {ƛ y M · N}{_}{x}{P} (ctxinj ▹β) = M [ x := P , y := v z ] [ z := N [ x := P ] ] , ctxinj ▹β , aux
  where σ = ι ≺+ (x , P)
        z = χ (σ , ƛ y M)
        z#σ = χ-lemma2 σ (ƛ y M)
        aux : M [ x := P , y := v z ] [ z := N [ x := P ] ] ∼α M [ y := N ] [ x := P ]
        aux = begin
                M [ x := P , y := v z ] [ z := N [ x := P ] ]
                ∼⟨ corollary1SubstLemma z#σ ⟩
                M [ x := P , y := N [ x := P ] ]
                ≈⟨ corollary1Prop7 {M}{N}{σ}{y} ⟩
                M [ y := N ] [ x := P ]
              ∎
subst-compat₁ {v _ · _} (ctxinj ())
subst-compat₁ {(_ · _) · _} (ctxinj ())
subst-compat₁ {v _} (ctxinj ())
subst-compat₁ {ƛ _ _} (ctxinj ())
subst-compat₁ (ctx·l c) = {!!}
subst-compat₁ (ctx·r c) = {!!}
subst-compat₁ (ctxƛ c) = {!!}

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

lemma-sn-v : ∀ (x : V) → sn (v x)
lemma-sn-v x = def λ x→M → ⊥-elim (var-irred x→M) 

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

-- start of overhead --

data sn² : Λ → Set where
  def : ∀ {M} → (∀ {N} → M ⟶² N → sn² N) → sn² M

β-then-βα : ∀ {M N} → M ⟶ N → M ⟶² N
β-then-βα {_}{N} M→N = N , M→N , ∼ρ

sn²→sn : ∀ {M} → sn² M → sn M
sn²→sn (def hi) = def λ M→N → sn²→sn (hi (β-then-βα M→N))

sn²-α : ∀ {M N} → M ∼α N → sn² M → sn² N
sn²-α = {!!}

sn→sn² : ∀ {M} → sn M → sn² M
sn→sn² {M} (def hi) = def λ {N} → λ { (P , M→P , P~N) → sn²-α P~N (sn→sn² (hi M→P)) }
  
-- end of overhead --

wkh-exp² : ∀ {M N x} → sn² N → sn² (M [ x := N ]) → sn² (ƛ x M · N)

wkh-exp²-aux : ∀ {M x N P} → sn² N → sn² (M [ x := N ]) → ƛ x M · N ⟶ P → sn² P
wkh-exp²-aux snN snM[x=N] (ctxinj ▹β) = snM[x=N]
wkh-exp²-aux snN snM[x=N] (ctx·l (ctxinj ()))
wkh-exp²-aux snN (def hi) (ctx·l (ctxƛ M→βM')) = wkh-exp² snN (hi (subst-compat₁ M→βM'))
wkh-exp²-aux {M}{x} (def hi) snM[x=N] (ctx·r N→βN') = wkh-exp² (hi (β-then-βα N→βN')) (sn→sn² (multistep (subst-compat₂ x M N→βN') (sn²→sn snM[x=N])))

wkh-exp² snN snM[x=N] = def λ { (_ , ƛxMN→Q , Q~P) → sn→sn² (sn-α Q~P (sn²→sn (wkh-exp²-aux snN snM[x=N] ƛxMN→Q))) }

wkh-exp : ∀ {M N x} → sn N → sn (M [ x := N ]) → sn (ƛ x M · N)
wkh-exp snN snM[x=N] = sn²→sn (wkh-exp² (sn→sn² snN) (sn→sn² snM[x=N]))

-- Lemma 11

closure→Ne : ∀ {R R'} → ne R → R ⟶ R' → ne R'
closure→Ne (nev x) (ctxinj ())
closure→Ne (ne· () N) (ctxinj ▹β)
closure→Ne (ne· R∈ne N) (ctx·l R→P) = ne· (closure→Ne R∈ne R→P) N
closure→Ne (ne· R∈ne N) (ctx·r {_}{_}{P} N→P) = ne· R∈ne P

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

lemma-ne : ∀ {M} → SNe M → ne M
lemma-ne (v x) = nev x
lemma-ne (app {_} {N} M∈ne _) = ne· (lemma-ne M∈ne) N

-- Theorem 1

sound-SN  : ∀ {M} → SN M → sn M

sound-SNe : ∀ {M} → SNe M → sn M

sound→SN  : ∀ {M N} → M →SN N → M →sn N

-- sound-SN : ∀ {M} → SN M → sn M
sound-SN (sne x) = sound-SNe x
sound-SN (abs x) = lemma-sn-ƛ (sound-SN x)
sound-SN (step M→N N∈Sn) = backward→sn (sound→SN M→N) (sound-SN N∈Sn)

-- sound-SNe : ∀ {M} → SNe M → sn M
sound-SNe (v x) = lemma-sn-v x
sound-SNe (app M∈SNe N∈Sn) = closure·Ne (lemma-ne M∈SNe) (sound-SNe M∈SNe) (sound-SN N∈Sn)

-- sound→SN : ∀ {M N} → M →SN N → M →sn N
sound→SN (β M∈Sn) = β (sound-SN M∈Sn)
sound→SN (appl M→M') = appl (sound→SN M→M')
