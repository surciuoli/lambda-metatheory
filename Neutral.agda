module Neutral where

open import Term
open import Chi
open import Substitution
open import Alpha
open import Beta
open import Relation Λ

open import Data.Sum
open import Relation.Binary.PropositionalEquality

_↠_ = _→α*_

-- Neutral/normal

data ne : V → Λ → Set
data nf : Λ → Set

data ne where
  var : ∀ {x} → ne x (v x)
  app : ∀ {x M N} → ne x M → nf N → ne x (M · N)

data nf where
  nfe : ∀ {M x} → ne x M → nf M
  abs : ∀ {x M} → nf M → nf (ƛ x M)

-- Weak-neutral

data wne : V → Λ → Set where
  var   : ∀ {x} → wne x (v x)
  app : ∀ {x M N} → wne x M → wne x (M · N)

-- Lemmas

closure-wne→β : ∀ {x M N} → wne x M → M →β N → wne x N
closure-wne→β var (ctxinj ())
closure-wne→β (app wneM) (ctx·l M→N) = app (closure-wne→β wneM M→N)
closure-wne→β (app wneM) (ctx·r _) = app wneM
closure-wne→β (app ()) (ctxinj ▹β)

closure-wne∼α : ∀ {x M N} → wne x M → M ∼α N → wne x N
closure-wne∼α var ∼v = var
closure-wne∼α (app wneM) (∼· M∼N _) = app (closure-wne∼α wneM M∼N)

lemma₁ : ∀ {x M N} → wne x M → M ↠ N → wne x N
lemma₁ wneM refl = wneM
lemma₁ wneM (just (inj₁ M→N)) = closure-wne→β wneM M→N
lemma₁ wneM (just (inj₂ M∼N)) = closure-wne∼α wneM M∼N
lemma₁ wneM (trans M→N N→P) = lemma₁ (lemma₁ wneM M→N) N→P 

corollary₁ : ∀ {x M} → wne x M → nf M → ne x M
corollary₁ var _ = var
corollary₁ (app wneM) (nfe (app neM nfN)) = app (corollary₁ wneM (nfe neM)) nfN

lemma₃ : ∀ {σ x y M} → wne x M → σ x ≡ v y → wne y (M ∙ σ)
lemma₃ {σ} {x} var σx≡y with σ x
lemma₃ var refl | v y = var
lemma₃ (app wneM) σx≡y = app (lemma₃ wneM σx≡y)
