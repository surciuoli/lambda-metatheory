module WeakNormalization where

open import Term
open import Chi
open import Substitution
open import Beta
open import ListProperties 

open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Data.Sum renaming (_⊎_ to _∨_)
open import Data.Product renaming (_×_ to _∧_) hiding (Σ)
open import Induction.WellFounded
open import Data.Product renaming (Σ to Σₓ)
open import Function using (id)
open import Relation.Binary
open import Data.Empty
open import Relation.Nullary
open import Data.Nat using (_≟_)
open import Relation using (just ; trans) renaming (refl to refl')

data Ne : V → Λ → Set
data Nf : Λ → Set

data Ne where
  v   : (x : V) → Ne x (v x)
  _·_ : ∀ {x r s} → Ne x r → Nf s → Ne x (r · s) 

data Nf where
  ne  : ∀ {x r} → Ne x r → Nf r
  ƛ : ∀ {x r} → Nf r → Nf (ƛ x r)

infix 4 _↓

data _↓ : Λ → Set where
  ↓nf : ∀ {r} → Nf r → r ↓
  ↓β  : ∀ {r r'} → r →α* r' → r' ↓ → r ↓ 

nf : ∀ {r} → r ↓ → ∃ (λ r' → r →α* r' ∧ Nf r') 
nf (↓nf {r} nfr) = r , refl' , nfr
nf (↓β r→*r' r'↓) with nf r'↓ 
... | r'' , r'→*r'' , nfr'' = r'' , trans r→*r' r'→*r'' , nfr''

infix 4 _<'_

data _<'_ : Type → Type → Set where
  <l : ∀ {α β} → α <' α ⟶ β
  <r : ∀ {α β} → β <' α ⟶ β

open Transitive-closure _<'_ renaming (_<⁺_ to _<_) 

_≤_ : Type → Type → Set
α ≤ β = α < β ∨ α ≡ β 

data isVar : Λ → Set where
  var : (x : V) → isVar (v x)
  
isVar? : (r : Λ) → Dec (isVar r)
isVar? (v x) = yes (var x)
isVar? (ƛ x r) = no (λ ())
isVar? (r · s) = no (λ ())

Π : Σ → Λ → Type → Cxt → Cxt → Set
Π σ r β Γ Δ = (σ ∶ Γ ⇀ Δ ⇂ r) ∧ (∀ {x} → x * r → isVar (σ x) ∨ (Nf (σ x) ∧ (Γ ⊢ v x ∶ β)))

Acc< : Type → Set
Acc< = Acc _<_

lemma₁ : ∀ {s Γ α β} → Acc< β → (r : Λ) → Nf r → Nf s → Γ ⊢ r ∶ β ⟶ α → Γ ⊢ s ∶ β → r · s ↓ 
lemma₂ : ∀ {Γ Δ α β σ} → Acc< β → (r : Λ) → Nf r → Γ ⊢ r ∶ α → Π σ r β Γ Δ → r ∙ σ ↓
lemma₃ : ∀ {x Γ Δ α β σ} → Acc< β → (r : Λ) → Ne x r → Γ ⊢ r ∶ α → Π σ r β Γ Δ → isVar (σ x) → ∃₂ (λ y → λ r' → Ne y r' ∧ r ∙ σ →α* r')
lemma₄ : ∀ {x Γ Δ α β σ} → Acc< β → (r : Λ) → Ne x r → Γ ⊢ r ∶ α → Π σ r β Γ Δ → ¬ isVar (σ x) → r ∙ σ ↓ ∧ α ≤ β 

lemma₁ _ .(v x) (ne (v x)) nfs _ _ = ↓nf (ne ((v x) · nfs))
lemma₁ _ (t · u) (ne netu) nfs _ _ = ↓nf (ne (netu · nfs))
lemma₁ {s}{Γ}.{α}.{β} accβ (ƛ x t) (ƛ nft) nfs (⊢ƛ .{x}{β}{α} Γ,x∶β⊢t:α) Γ⊢s∶β = ↓β ƛxts→α*tx=s (lemma₂ accβ t nft Γ,x∶β⊢t:α Πx=s)
  where
    x=s : Σ
    x=s = ι ≺+ (x , s)
    Πx=s : Π x=s t β (Γ ‚ x ∶ β) Γ
    x∈Γ‚x∶β : x ∈ (Γ ‚ x ∶ β)
    x∈Γ‚x∶β = here refl
    Γ‚x∶β⊢x∶β : (Γ ‚ x ∶ β) ⊢ v x ∶ β
    Γ‚x∶β⊢x∶β = ⊢v x∈Γ‚x∶β 
    isVar∨Nf : ∀ {y} → y * t → isVar (x=s y) ∨ (Nf (x=s y) ∧ ((Γ ‚ x ∶ β) ⊢ v y ∶ β))
    isVar∨Nf {y} _ with x ≟ y
    isVar∨Nf .{x} _  | yes refl = inj₂ (nfs , Γ‚x∶β⊢x∶β)
    ... | no _ = inj₁ (var y)
    Πx=s = lemma⇀ (lemmaι≺+⇀ Γ⊢s∶β) , isVar∨Nf
    ƛxts→α*tx=s : ƛ x t · s →α* t ∙ x=s
    ƛxts→α*tx=s = just (inj₁ (ctxinj ▹β)) 

x*ₓr : ∀ {x r} → Ne x r → x * r
x*ₓr (v x) = *v
x*ₓr (tₓ · _) = *·l (x*ₓr tₓ)

lemma₂-aux : ∀ {x r Γ Δ α β σ} → Acc< β → Ne x r → Γ ⊢ r ∶ α → Π σ r β Γ Δ → r ∙ σ ↓
lemma₂-aux {x}{r}{_}{_}{_}{_}{σ} accβ ner r∶α Πσ with isVar? (σ x)
... | no ¬isVarσx = proj₁ (lemma₄ accβ r ner r∶α Πσ ¬isVarσx)
... | yes isVarσx with lemma₃ accβ r ner r∶α Πσ isVarσx
...   | _ , _ , neyr' , rσ→α*r' = ↓β rσ→α*r' (↓nf (ne neyr'))

ƛ↓ : ∀ {r} → (x : V) → r ↓ → ƛ x r ↓
ƛ↓ {r} x r↓ with nf r↓
... | r' , r→*r' , nfr' = ↓β (abs-star r→*r') (↓nf (ƛ nfr'))

lemma₂ accβ .(v x) (ne (v x)) = lemma₂-aux accβ (v x)
lemma₂ accβ (t · u) (ne netu) = lemma₂-aux accβ netu
lemma₂ {Γ}{Δ}{_}{β}{σ} accβ (ƛ y t) (ƛ nft) (⊢ƛ {_}{γ}{α} Γ,y∶γ⊢t:α) Πσ = ƛ↓ z (lemma₂ accβ t nft Γ,y∶γ⊢t:α Πσ,y=z)
  where
    z : V
    z = χ (σ , ƛ y t)
    σ,y=z : Σ
    σ,y=z = σ ≺+ (y , v z)
    z#σ⇂λyt : z #⇂ (σ , ƛ y t)
    z#σ⇂λyt = χ-lemma2 σ (ƛ y t)
    Πσ,y=z-aux : ∀ {x} → (x * t) → (isVar (σ,y=z x) ∨ (Nf (σ,y=z x) ∧ (Γ ‚ y ∶ γ ⊢ v x ∶ β)))
    Πσ,y=z-aux {x} x*t with y ≟ x
    Πσ,y=z-aux .{y} _ | yes refl = inj₁ (var z)
    ... | no y≢x with (proj₂ Πσ) (*ƛ x*t y≢x)
    ...   | inj₁ isVarσx = inj₁ isVarσx 
    ...   | inj₂ (Nfσx , Γ⊢x∶β) = inj₂ (Nfσx , Γ‚y∶γ⊢x∶β)
      where
        Γ‚y∶γ⊢x∶β : Γ ‚ y ∶ γ ⊢ v x ∶ β
        Γ‚y∶γ⊢x∶β = lemmaWeakening⊢# (#v (sym≢ y≢x)) Γ⊢x∶β
    Πσ,y=z : Π σ,y=z t β (Γ ‚ y ∶ γ) (Δ ‚ z ∶ γ)
    Πσ,y=z = lemmaaux⇀ z#σ⇂λyt (proj₁ Πσ) , Πσ,y=z-aux

isVar→∃y : ∀ {r} → isVar r → ∃ (λ y → r ≡ v y)
isVar→∃y .{v x} (var x) = x , refl

Πtu→Πt : ∀ {σ t u β Γ Δ} → Π σ (t · u) β Γ Δ → Π σ t β Γ Δ
Πtu→Πt {_}{t}{_}{_}{Γ} (σ∶Γ⇀Δ⇂t·u , λx*t·u→isVar∨Nf) =
  (λ {x : V}(x*t : x * t)(x∈Γ : x ∈ Γ) → σ∶Γ⇀Δ⇂t·u (*·l x*t) x∈Γ) , (λ {x}(x*t : x * t) → λx*t·u→isVar∨Nf (*·l x*t))

Πtu→Πu : ∀ {σ t u β Γ Δ} → Π σ (t · u) β Γ Δ → Π σ u β Γ Δ
Πtu→Πu {_}{_}{u}{_}{Γ} (σ∶Γ⇀Δ⇂t·u , λx*t·u→isVar∨Nf) =
  (λ {x : V}(x*u : x * u)(x∈Γ : x ∈ Γ) → σ∶Γ⇀Δ⇂t·u (*·r x*u) x∈Γ) , (λ {x}(x*u : x * u) → λx*t·u→isVar∨Nf (*·r x*u))

→α*t·u : ∀ {t u t' u'} → t →α* t' → u →α* u' → t · u →α* t' · u'
→α*t·u t→*t' u→*u' = trans (app-star-l t→*t') (app-star-r u→*u')

lemma₃ .{x}{_}{_}{_}{_}{σ} _ .(v x) (v x) _ _ isVarσx with σ x | isVar→∃y isVarσx
... | .(v y) | y , refl = y , v y , v y , refl'
lemma₃  {_}{Γ}{Δ}.{α}{β}{σ} accβ .(t · u) (net · nfu) (⊢· {γ}{α}{t}{u} t∶γ→α u∶γ) Πσ isVarσx
  with lemma₃ accβ t net t∶γ→α (Πtu→Πt Πσ) isVarσx | nf (lemma₂ accβ u nfu u∶γ (Πtu→Πu Πσ))
... | x , t' , neₓt' , tσ→t' | u' , uσ→*u' , nfu' = x , t' · u' , neₓt' · nfu' , →α*t·u tσ→t' uσ→*u'

γ⟶α≤β→γ<β : ∀ {γ α β} → (γ ⟶ α) ≤ β → γ < β
γ⟶α≤β→γ<β (inj₁ γ⟶α<β) = trans [ <l ] γ⟶α<β 
γ⟶α≤β→γ<β (inj₂ refl) = [ <l ]

γ⟶α≤β→α<β : ∀ {γ α β} → (γ ⟶ α) ≤ β → α < β
γ⟶α≤β→α<β (inj₁ γ⟶α<β) =  trans [ <r ] γ⟶α<β
γ⟶α≤β→α<β (inj₂ refl) = [ <r ]

Γ⊢x∶α≡β : ∀ {Γ x α β} → Γ ⊢ v x ∶ α → Γ ⊢ v x ∶ β → α ≡ β
Γ⊢x∶α≡β {Γ}{_}{_}{_} (⊢v {x} x∈Γ₁) (⊢v .{x} x∈Γ₂) = lemma∈!⟨⟩ x∈Γ₁ x∈Γ₂

lemma₄ .{x}{_}{_}{α}{β} _ .(v x) (v x) Γ⊢x∶α Πσ ¬isVarσx with (proj₂ Πσ) (x*ₓr (v x))
... | inj₁ isVarσx = ⊥-elim (¬isVarσx isVarσx)
... | inj₂ (Nfσx , Γ⊢x∶β) = ↓nf Nfσx , inj₂ (Γ⊢x∶α≡β Γ⊢x∶α Γ⊢x∶β)
lemma₄ {_}{Γ}{Δ}.{α}{β}{σ} (acc h<β) .(t · u) (net · nfu) (⊢· {γ}{α}{t}{u} t∶γ⟶α u∶γ) Πσ ¬isVarσx
  with map₁ nf (lemma₄ (acc h<β) t net t∶γ⟶α (Πtu→Πt Πσ) ¬isVarσx) | nf (lemma₂ (acc h<β) u nfu u∶γ (Πtu→Πu Πσ))
    where
      map₁ : {A B C : Set} → (A → C) → A × B → C × B
      map₁ f (a , b) = (f a , b)
... | (t' , tσ→*t' , nft') , γ⟶α≤β | u' , (uσ→*u' , nfu') = ↓β t·uσ→*t'u' (lemma₁ (h<β γ γ<β) t' nft' nfu' Δ⊢t'∶γ⟶α Δ⊢u'∶γ) , α≤β 
  where
    α≤β : α ≤ β
    α≤β = inj₁ (γ⟶α≤β→α<β γ⟶α≤β)
    γ<β : γ < β
    γ<β = γ⟶α≤β→γ<β γ⟶α≤β
    Δ⊢tσ:γ⟶α : Δ ⊢ t ∙ σ ∶ γ ⟶ α
    Δ⊢tσ:γ⟶α = lemma⊢σM t∶γ⟶α (proj₁ (Πtu→Πt Πσ))
    Δ⊢uσ:γ : Δ ⊢ u ∙ σ ∶ γ
    Δ⊢uσ:γ = lemma⊢σM u∶γ (proj₁ (Πtu→Πu Πσ))    
    Δ⊢t'∶γ⟶α : Δ ⊢ t' ∶ γ ⟶ α
    Δ⊢t'∶γ⟶α = lemma⊢→α* Δ⊢tσ:γ⟶α tσ→*t'
    Δ⊢u'∶γ : Δ ⊢ u' ∶ γ
    Δ⊢u'∶γ = lemma⊢→α* Δ⊢uσ:γ uσ→*u'
    t·uσ→*t'u' : (t · u) ∙ σ →α* t' · u'
    t·uσ→*t'u' = →α*t·u tσ→*t' uσ→*u'

wf<' : Well-founded _<'_
wf<' τ = acc λ y ()
wf<' (α ⟶ β) = acc accind
  where accind : (γ : Type) → γ <' (α ⟶ β) → Acc _<'_ γ
        accind .α <l = wf<' α
        accind .β <r = wf<' β

wf< : Well-founded _<_
wf< = well-founded wf<'

wk : ∀ {r Γ α} → Γ ⊢ r ∶ α → r ↓
wk {v x}   _ = ↓nf (ne (v x))
wk {ƛ x r} (⊢ƛ Γ‚x∶α⊢r∶β) = ƛ↓ x (wk Γ‚x∶α⊢r∶β)
wk {r · s} (⊢·{β} Γ⊢r∶β⟶α Γ⊢s:β) with nf (wk Γ⊢r∶β⟶α) | nf (wk Γ⊢s:β) 
... | r' , r→*r' , nfr' | s' , s→*s' , nfs' = ↓β (→α*t·u r→*r' s→*s') (lemma₁ (wf< β) r' nfr' nfs' (lemma⊢→α* Γ⊢r∶β⟶α r→*r') (lemma⊢→α* Γ⊢s:β s→*s'))
