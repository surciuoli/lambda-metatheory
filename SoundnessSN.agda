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
open import Substitution
open import Alpha
open import Relation

open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Relation.Binary.Core
open import Data.Product
open import Data.Nat

infix 5 _⟶_
infix 5 _→*_
infix 5 _→sn_
infix 30 _[_:=_]
infix 5 _→SN_

_⟶_ : Λ → Λ → Set
M ⟶ N = M →α N

_→*_ : Λ → Λ → Set
M →* N = M →α* N

_[_:=_] : Λ → V → Λ → Λ
M [ x := N ] =  M ∙ ι ≺+ (x , N)

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
  
-- Auxiliary lemmas

var-irred : ∀ {x M} → ¬ (x ⟶ M)
var-irred = {!!}

ne~α : ∀ {M N} → ne M → M ∼α N → ne N
ne~α = {!!}

α-lr : ∀ {t u t' u'} → t →α* t' → u →α* u' → t · u →α* t' · u'
α-lr t→*t' u→*u' = trans (app-star-l t→*t') (app-star-r u→*u')

-- Lemma 5

clos→α-under-σ : ∀ {M N σ} → M →α N → M ∙ σ →α N ∙ σ
clos→α-under-σ = {!!}

-- Lemma 6

lemma6-5 : ∀ {M x N N'} → N ⟶ N' → M [ x := N ] →* M [ x := N' ]
lemma6-5 {v y}{x} N→N' with x ≟ y
... | yes _ = just N→N'
... | no _ = refl
lemma6-5 {M · N}{x} N→N' = α-lr (lemma6-5 {M}{x} N→N') (lemma6-5 {N}{x} N→N')
lemma6-5 {ƛ y M}{x} N→N' = {!!} -- abs-star {y} (lemma6-5 {M}{x} N→N')

-- Lemma 8

multistep : ∀ {M M'} → M →* M' → sn M → sn M'
multistep = {!!}

-- Lemma 9

lemma-sn-v : ∀ x → sn (v x)
lemma-sn-v x = def λ x⇢M → ⊥-elim (var-irred x⇢M) 

lemma-sn-ƛ : ∀ {x M} → sn M → sn (ƛ x M)
lemma-sn-ƛ = {!!}

lemma-sn-app : ∀ {M N} → sn (M · N) → sn M × sn N
lemma-sn-app = {!!}

-- Lemma 10 (Weak head expansion)

wkh-exp : ∀ {M N x} → sn N → sn (M [ x := N ]) → sn (ƛ x M · N)

wkh-exp-aux : ∀ {M N x P} → sn N → sn (M [ x := N ]) → ƛ x M · N ⟶ P → sn P
wkh-exp-aux snN snM[x=N] (inj₁ (ctxinj ▹β)) = snM[x=N]
wkh-exp-aux snN snM[x=N] (inj₁ (ctx·l (ctxinj ())))
wkh-exp-aux snN (def M[x=N]→P⇒snP) (inj₁ (ctx·l (ctxƛ M→βM'))) = wkh-exp snN (M[x=N]→P⇒snP (clos→α-under-σ (inj₁ M→βM')))
wkh-exp-aux {M}{_}{x} (def N→P⇒snP) snM[x=N] (inj₁ (ctx·r N→βN')) = wkh-exp (N→P⇒snP (inj₁ N→βN')) (multistep (lemma6-5 {M}{x = x} (inj₁ N→βN')) snM[x=N])
wkh-exp-aux snN snM[x=N] (inj₂ y) = {!!}

-- wkh-exp : ∀ {M N x} → sn N → sn (M [ x := N ]) → sn (ƛ x M · N)
wkh-exp snN snM[x=N] = def λ ƛxMN→P → wkh-exp-aux snN snM[x=N] ƛxMN→P 

-- Lemma 11

closure→Ne : ∀ {R R'} → ne R → R ⟶ R' → ne R'
closure→Ne (nev x) x→x' = ⊥-elim (var-irred x→x')
closure→Ne (ne· () N) (inj₁ (ctxinj ▹β))
closure→Ne (ne· R∈ne N) (inj₁ (ctx·l R→P)) = ne· (closure→Ne R∈ne (inj₁ R→P)) N
closure→Ne (ne· R∈ne N) (inj₁ (ctx·r {_}{_}{P} N→P)) = ne· R∈ne P
closure→Ne R∈ne (inj₂ R~R') = ne~α R∈ne R~R'

closure·Ne : ∀ {R N} → ne R → sn R → sn N → sn (R · N)

closure·Ne-aux : ∀ {R N Q} → ne R → sn R → sn N → R · N ⟶ Q → sn Q
closure·Ne-aux () snR snN (inj₁ (ctxinj ▹β))
closure·Ne-aux neR (def R→P⇒snP) snN (inj₁ (ctx·l R→R')) = closure·Ne (closure→Ne neR (inj₁ R→R')) (R→P⇒snP (inj₁ R→R')) snN
closure·Ne-aux neR snR (def N→P⇒snP) (inj₁ (ctx·r N→N')) = closure·Ne neR snR (N→P⇒snP (inj₁ N→N'))
closure·Ne-aux neR snR snN (inj₂ y) = {!!}

-- closure·Ne : ∀ {R N} → ne R → sn R → sn N → sn (R · N)
closure·Ne R∈ne R∈sn N∈sn = def λ RN→Q → closure·Ne-aux R∈ne R∈sn N∈sn RN→Q

-- Lemma 12 (Confluence)

confluence : ∀ {M N N'} → M →sn N → M ⟶ N' → N ≡ N' ⊎ ∃ (λ Q → N' →sn Q × N →* Q)
confluence (β _) (inj₁ (ctxinj ▹β)) = inj₁ refl
confluence {ƛ x M · N} (β N∈sn) (inj₁ (ctx·l (ctxƛ {._}{._}{M'} M→M'))) = inj₂ (M' [ x := N ] , β N∈sn , just (clos→α-under-σ (inj₁ M→M'))) 
confluence (β _) (inj₁ (ctx·l (ctxinj ())))
confluence {ƛ x M · N} (β (def N→N'⇒N∈sn)) (inj₁ (ctx·r .{_}{._}{N'} N→N')) =
  inj₂ (M [ x := N' ] , β (N→N'⇒N∈sn (inj₁ N→N')) , lemma6-5 {M}{x}{N}{N'} (inj₁ N→N'))
confluence (β _) (inj₂ (∼· (∼ƛ x₂ x₃ x₄) N~N')) = {!!}
confluence (appl ()) (inj₁ (ctxinj ▹β))
confluence {M · N} (appl M→snM') (inj₁ (ctx·l M→M₂)) with confluence M→snM' (inj₁ M→M₂)
... | inj₁ refl = inj₁ refl
... | inj₂ (P , M₂→snP , M'→*P) = inj₂ (P · N , appl M₂→snP , app-star-l M'→*P)
confluence {M · N}{M' · .N}{.M · N'} (appl M→snM') (inj₁ (ctx·r N→N')) = inj₂ (M' · N' , appl M→snM' , just (app-step-r (inj₁ N→N')))
confluence (appl M→snM') (inj₂ y) = {!!}

-- Lemma 13

backward→sn-aux : ∀ {M N M'} → sn M → sn N → M →sn M' → sn (M' · N) → sn (M · N)

backward→sn-aux' : ∀ {M N M' Q} → M · N ⟶ Q → sn M → sn N → M →sn M' → sn (M' · N) → sn Q
backward→sn-aux' (inj₁ (ctxinj ▹β)) _ _ () _
backward→sn-aux' {.M} {.N} (inj₁ (ctx·l {M} {M''} {N} M→M'')) (def M→Q⇒Q∈sn) N∈sn M→snM' M'N∈sn with confluence M→snM' (inj₁ M→M'')
... | inj₁ refl = M'N∈sn
... | inj₂ (P , M''→snP , M'→*P) = backward→sn-aux (M→Q⇒Q∈sn (inj₁ M→M'')) N∈sn M''→snP (multistep (app-star-l M'→*P) M'N∈sn )
backward→sn-aux' {_}{N}{M'} (inj₁ (ctx·r {_}{_}{N'} N→N')) M∈sn (def N→Q⇒Q∈sn) M→snM' (def M'N→Q⇒Q∈sn) =
  backward→sn-aux M∈sn (N→Q⇒Q∈sn (inj₁ N→N')) M→snM' (M'N→Q⇒Q∈sn (app-step-r (inj₁ N→N')))
backward→sn-aux' (inj₂ MN~αM'N') M∈sn N∈sn M→snM' M'N∈sn = {!!}

-- backward→sn-aux : ∀ {M N M'} → sn M → sn N → M →sn M' → sn (M' · N) → sn (M · N)
backward→sn-aux M∈sn N∈Sn M→snM' M'N∈sn = def λ MN→Q → backward→sn-aux' MN→Q M∈sn N∈Sn M→snM' M'N∈sn

backward→sn : ∀ {M M'} → M →sn M' → sn M' → sn M
backward→sn (β N∈sn) M[x=N]∈sn = wkh-exp N∈sn M[x=N]∈sn
backward→sn {M · N} {M' · .N} (appl M→M') M'N∈sn = let snM' , snN = lemma-sn-app M'N∈sn
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
