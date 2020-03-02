module SubstitutionCompatibilityLemmas where

open import Chi
open import Term 
open import Beta
open import Substitution
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
open import Relation.Binary.PropositionalEquality using (sym; subst₂; refl)

infix 5 _↠_ 
infix 30 _[_:=_]
infix 30 _[_∣_:=_]

_↠_ = _→α*_

_[_:=_] : Λ → V → Λ → Λ
M [ x := N ] =  M ∙ ι ≺+ (x , N)

_[_∣_:=_] : Λ → Σ → V → Λ → Λ
M [ σ ∣ y := P ] = M ∙ σ ≺+ (y , P)

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

subst-compat→β : ∀ {M N σ} → M →β N → ∃ λ P → M ∙ σ →β P × P ∼α N ∙ σ
subst-compat→β {ƛ y M · N}{_}{σ} (ctxinj ▹β) = M [ σ ∣ y := v z ] [ z := N ∙ σ ] , ctxinj ▹β , lemma∼α∙ z#σ
  where z = χ (σ , ƛ y M)
        z#σ = χ-lemma2 σ (ƛ y M)
subst-compat→β {v _ · _} (ctxinj ())
subst-compat→β {(_ · _) · _} (ctxinj ())
subst-compat→β {v _} (ctxinj ())
subst-compat→β {ƛ _ _} (ctxinj ())
subst-compat→β {_ · N}{_}{σ} (ctx·l M→M') =
  let Q , Mσ→Q , Q~M'σ = subst-compat→β M→M'
  in Q · (N ∙ σ) , ctx·l Mσ→Q , ∼· Q~M'σ ∼ρ
subst-compat→β {M · _}{_}{σ} (ctx·r N→N') =
  let Q , Nσ→Q , Q~N'σ = subst-compat→β N→N'
  in (M ∙ σ) · Q , ctx·r Nσ→Q , ∼· ∼ρ Q~N'σ
subst-compat→β {ƛ x M}{ƛ .x M'}{σ} (ctxƛ M→M') =
  let z = χ (σ , ƛ x M)
      z#σ = χ-lemma2 σ (ƛ x M)
      N , Mσ,z/x→N , N~M'σ,z/x = subst-compat→β {M}{M'} M→M'
      aux = begin
              ƛ z N
              ∼⟨ lemma∼λ N~M'σ,z/x ⟩
              ƛ z (M' [ σ ∣ x := v z ])
              ∼⟨ ∼σ (corollary4-2 (#⇂-preservedby-β (ctxƛ M→M') z#σ)) ⟩
              ƛ x M' ∙ σ
            ∎
  in ƛ z N , ctxƛ Mσ,z/x→N , aux

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

conflα→β : ∀ {M N P} → M ∼α N → M →β P → ∃ λ Q → N →β Q × P ∼α Q
conflα→β ∼v (ctxinj ())
conflα→β {ƛ x M · N}{ƛ y M' · N'} ƛxMN∼ƛyM'N' (ctxinj ▹β) = M' [ y := N' ] , ctxinj ▹β , β-equiv ƛxMN∼ƛyM'N'
conflα→β (∼· ∼v _) (ctxinj ())
conflα→β (∼· (∼· _ _) _) (ctxinj ())
conflα→β (∼· {_}{_}{_}{N'} M~M' N~N') (ctx·l M→M'') with conflα→β M~M' M→M''
... | P , M'→P , M''~P = P · N' , ctx·l M'→P , ∼· M''~P N~N'
conflα→β (∼· {_}{M'}{_}{_} M~M' N~N') (ctx·r N→N'') with conflα→β N~N' N→N''
... | P , N'→P , N''~P = M' · P , ctx·r N'→P , ∼· M~M' N''~P
conflα→β (∼ƛ _ _ _) (ctxinj ())
conflα→β {ƛ x M}{ƛ x' M'}{ƛ .x N} (∼ƛ {_}{_}{_}{.x'}{y} y#ƛxM y#ƛx'M' M[y/x]~M'[y/x']) (ctxƛ M→N) = 
  let ƛxM~ƛx'M' = (∼ƛ y#ƛxM y#ƛx'M' M[y/x]~M'[y/x'])
      K₁ , M[x'/x]→K₁ , K₁∼N[x'/x] = subst-compat→β {σ = ι ≺+ (x , v x')} M→N
      M[x'/x]~M' = lemma-α-ren ƛxM~ƛx'M'
      K₂ , M'→K₂ , K₁∼K₂ = conflα→β M[x'/x]~M' M[x'/x]→K₁
      ƛx'M'→ƛx'K₂ = ctxƛ {x = x'} M'→K₂
      x'#ƛxN = lemma→β# (lemmaM∼N# (∼σ ƛxM~ƛx'M') x' #ƛ≡) (ctxƛ M→N)
      ƛx'K₂∼ƛxN = ∼τ (lemma∼λ {x = x'} (∼τ (∼σ K₁∼K₂) K₁∼N[x'/x])) (∼σ (corollary4-2' x'#ƛxN))
  in ƛ x' K₂ , ƛx'M'→ƛx'K₂ , ∼σ ƛx'K₂∼ƛxN

conflα↠ : ∀ {M N P} → M ∼α N → M ↠ P → ∃ λ Q → N ↠ Q × P ∼α Q
conflα↠ {M} {N} {.M} M∼N refl = N , refl , M∼N
conflα↠ M∼N (just (inj₁ M→P)) =
  let Q , N→Q , P∼Q = conflα→β M∼N M→P
  in Q , just (inj₁ N→Q) , P∼Q
conflα↠ {M} M∼N (just (inj₂ M∼P)) = M , just (inj₂ (∼σ M∼N)) , ∼σ M∼P
conflα↠ M∼N (trans M→P P→Q) =
  let R , N→R , P∼R = conflα↠ M∼N M→P
      S , R→S , Q∼S = conflα↠ P∼R P→Q
  in S , trans N→R R→S , Q∼S

subst-compat : ∀ {N N'} → (x : V) → (M : Λ) → N →β N' → M [ x := N ] ↠ M [ x := N' ]
subst-compat x M N→N' = lemma⇉⊆→α* (lemma⇉ (⇉ρ {M}) (corollary⇉ₛ≺+ x (lemma→α⊆⇉ (inj₁ N→N'))))

subst-compat↠ : ∀ {M N σ} → M ↠ N → (M ∙ σ) ↠ (N ∙ σ)
subst-compat↠ refl = refl
subst-compat↠ (just (inj₁ M→βN)) =
  let P , Mσ→βP , P∼Nσ = subst-compat→β M→βN
  in trans (just (inj₁ Mσ→βP)) (just (inj₂ P∼Nσ))
subst-compat↠ {M} {N} {σ} (just (inj₂ M∼N)) with M ∙ σ | N ∙ σ | lemmaM∼M'→Mσ≡M'σ {M} {N} {σ} M∼N
... | P | .P | refl = refl
subst-compat↠ (trans M↠N N↠P) = trans (subst-compat↠ M↠N) (subst-compat↠ N↠P)
