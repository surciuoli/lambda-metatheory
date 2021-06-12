module SoundnessSN where

open import Chi
open import Term renaming (_⟶_ to _⇒_) hiding (_∶_)
open import Beta renaming (_→α*_ to _↠_)
open import Substitution hiding (_∘_)
open import Alpha
open import Relation Λ 
open import ParallelReduction
open import SubstitutionLemmas
open import SubstitutionCompatibilityLemmas hiding (_↠_)
open import Neutral using (wne; var; app)
open import SN

open import Relation.Nullary
open import Data.Empty
open import Data.Sum
open import Relation.Binary.Core hiding (Rel)
open import Data.Product hiding (Σ)
open import Data.Nat hiding (_≟_)
open import Function
open import Relation.Binary.PropositionalEquality using (sym; subst₂)

infix 5 _→sn_

data sn : Λ → Set where
  def : ∀ {M} → (∀ {N} → M →β N → sn N) → sn M

data _→sn_ : Λ → Λ → Set where
  β    : ∀ {x M N} → sn N → ƛ x M · N →sn M [ x := N ]
  appl : ∀ {M M' N} → M →sn M' → M · N →sn M' · N

sn-α : ∀ {M N} → M ∼α N → sn M → sn N
sn-α {_}{N} M~N (def hi) = def λ N→P → sn-α-aux N→P
  where sn-α-aux : ∀ {P} → N →β P → sn P
        sn-α-aux N→P with conflα→β (∼σ M~N) N→P
        ... | _ , M→Q , P~Q = sn-α (∼σ P~Q) (hi M→Q)

var-irred : ∀ {x M} → (v x) →β M → ⊥ 
var-irred (ctxinj ())

⟶²⇒⟶* : ∀ {M N P} → M →β N × N ∼α P → M ↠ P
⟶²⇒⟶* (M→P , P~N) = trans (just (inj₁ M→P)) (just (inj₂ P~N))

multistep : ∀ {M M'} → M ↠ M' → sn M → sn M'
multistep refl snM = snM
multistep (just (inj₁ M→M')) (def snM) = snM M→M'
multistep (just (inj₂ M~M')) snM = sn-α M~M' snM
multistep (trans M→*N N→*P) snM = multistep N→*P (multistep M→*N snM)

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

wkh-exp-α : ∀ {M N x Q} → sn N → sn Q → Q ∼α M [ x := N ] → sn (ƛ x M · N)
wkh-exp-α-aux : ∀ {M x N P Q} → sn N → sn Q → Q ∼α M [ x := N ] → ƛ x M · N →β P → sn P

wkh-exp-α-aux snN snQ Q~M[N/x] (ctxinj ▹β) = sn-α Q~M[N/x] snQ
wkh-exp-α-aux _ _ _ (ctx·l (ctxinj ()))
wkh-exp-α-aux {_}{x} snN (def hi) Q~M[N/x] (ctx·l (ctxƛ M→M')) =
  let _ , M[N/x]→R , R~M'[N/x] = subst-compat→β M→M'
      _ , Q→S , R~S  = conflα→β (∼σ Q~M[N/x]) M[N/x]→R
  in wkh-exp-α snN (hi Q→S) (∼τ (∼σ R~S) R~M'[N/x])
wkh-exp-α-aux {M}{x} (def hi) snQ Q~M[N/x] (ctx·r N→N') = wkh-exp-α (hi N→N') (multistep (subst-compat x M N→N') (sn-α Q~M[N/x] snQ)) ∼ρ
wkh-exp-α snN snQ Q~M[N/x] = def λ ƛxMN→Q → wkh-exp-α-aux snN snQ Q~M[N/x] ƛxMN→Q

wkh-exp : ∀ {M N x} → sn N → sn (M [ x := N ]) → sn (ƛ x M · N)
wkh-exp snN snM[N/x] = wkh-exp-α snN snM[N/x] ∼ρ

closure→Ne : ∀ {R R' x} → wne x R → R →β R' → wne x R'
closure→Ne var (ctxinj ())
closure→Ne (app ()) (ctxinj ▹β)
closure→Ne (app R∈ne) (ctx·l R→P) = app (closure→Ne R∈ne R→P)
closure→Ne (app R∈ne) (ctx·r {_}{_}{P} N→P) = app R∈ne

closure·Ne : ∀ {R N x} → wne x R → sn R → sn N → sn (R · N)
closure·Ne-aux : ∀ {R N Q x} → wne x R → sn R → sn N → R · N →β Q → sn Q

closure·Ne-aux () snR snN (ctxinj ▹β)
closure·Ne-aux neR (def R→P⇒snP) snN (ctx·l R→R') = closure·Ne (closure→Ne neR R→R') (R→P⇒snP R→R') snN
closure·Ne-aux neR snR (def N→P⇒snP) (ctx·r N→N') = closure·Ne neR snR (N→P⇒snP N→N')
closure·Ne R∈ne R∈sn N∈sn = def λ RN→Q → closure·Ne-aux R∈ne R∈sn N∈sn RN→Q

confluence : ∀ {M N N'} → M →sn N → M →β N' → N ∼α N' ⊎ ∃ (λ Q → N' →sn Q × N ↠ Q)
confluence (β _) (ctxinj ▹β) = inj₁ ∼ρ
confluence {ƛ x M · N} (β N∈sn) (ctx·l (ctxƛ {._}{._}{M'} M→M')) = inj₂ (M' [ x := N ] , β N∈sn , ⟶²⇒⟶* (proj₂ (subst-compat→β M→M')))
confluence (β _) (ctx·l (ctxinj ()))
confluence {ƛ x M · N} (β (def N→N'⇒N∈sn)) (ctx·r .{_}{._}{N'} N→N') = inj₂ (M [ x := N' ] , β (N→N'⇒N∈sn N→N') , subst-compat x M N→N')
confluence (appl (appl _)) (ctxinj ())
confluence (appl (β _)) (ctxinj ())
confluence {M · N} (appl M→snM') (ctx·l M→M₂) with confluence M→snM' M→M₂
... | inj₁ M'∼M₂ = inj₁ (∼· M'∼M₂ ∼ρ)
... | inj₂ (P , M₂→snP , M'→*P) = inj₂ (P · N , appl M₂→snP , app-star-l M'→*P)
confluence {M · N}{M' · .N}{.M · N'} (appl M→snM') (ctx·r N→N') = inj₂ (M' · N' , appl M→snM' , just (app-step-r (inj₁ N→N')))

backward→sn-aux : ∀ {M N M'} → sn M → sn N → M →sn M' → sn (M' · N) → sn (M · N)
backward→sn-aux' : ∀ {M N M' Q} → M · N →β Q → sn M → sn N → M →sn M' → sn (M' · N) → sn Q

backward→sn-aux' (ctxinj ▹β) _ _ () _ 
backward→sn-aux' {.M} {.N} (ctx·l {M} {M''} {N} M→M'') (def M→Q⇒Q∈sn) N∈sn M→snM' M'N∈sn with confluence M→snM' M→M''
... | inj₁ M'∼M'' = sn-α (∼· M'∼M'' ∼ρ) M'N∈sn
... | inj₂ (P , M''→snP , M'→*P) = backward→sn-aux (M→Q⇒Q∈sn M→M'') N∈sn M''→snP (multistep (app-star-l M'→*P) M'N∈sn )
backward→sn-aux' {_}{N}{M'} (ctx·r {_}{_}{N'} N→N') M∈sn (def N→Q⇒Q∈sn) M→snM' (def M'N→Q⇒Q∈sn) =
  backward→sn-aux M∈sn (N→Q⇒Q∈sn N→N') M→snM' (M'N→Q⇒Q∈sn (ctx·r N→N'))
backward→sn-aux M∈sn N∈Sn M→snM' M'N∈sn = def λ MN→Q → backward→sn-aux' MN→Q M∈sn N∈Sn M→snM' M'N∈sn

backward→sn : ∀ {M M'} → M →sn M' → sn M' → sn M
backward→sn (β N∈sn) M[x=N]∈sn = wkh-exp N∈sn M[x=N]∈sn
backward→sn {M · N} {M' · .N} (appl M→M') M'N∈sn = let snM' , snN = inv-app-lemma M'N∈sn
                                                   in backward→sn-aux (backward→sn M→M' snM') snN M→M' M'N∈sn

lemma-ne : ∀ {M x} → SNe x M → wne x M
lemma-ne v = var
lemma-ne (app M∈ne _) = app (lemma-ne M∈ne)

sound-SN  : ∀ {M} → SN M → sn M
sound-SNe : ∀ {M x} → SNe x M → sn M
sound→SN  : ∀ {M N} → M →SN N → M →sn N

sound-SN (sne x) = sound-SNe x
sound-SN (abs x) = lemma-sn-ƛ (sound-SN x)
sound-SN (exp M→N N∈Sn) = backward→sn (sound→SN M→N) (sound-SN N∈Sn)
sound-SNe v = lemma-sn-v
sound-SNe (app M∈SNe N∈Sn) = closure·Ne (lemma-ne M∈SNe) (sound-SNe M∈SNe) (sound-SN N∈Sn)
sound→SN (β M∈Sn) = β (sound-SN M∈Sn)
sound→SN (appl M→M') = appl (sound→SN M→M')
