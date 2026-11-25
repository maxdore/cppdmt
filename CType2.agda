{-# OPTIONS --cubical --guardedness --safe #-}

module CType2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.HITs.S1
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout

open import Prelude
open import ComplexMatching

private
  variable
    ℓ : Level

CType² : Type (ℓ-suc ℓ)
CType² {ℓ} = Σ[ A ∈ Type ℓ ] Σ[ B ∈ (A → A → Type ℓ) ] (∀{a b c d} → B a b → B c d → B a c → B b d → Type ℓ)

data ∣_∣ (C : CType² {ℓ}) : Type ℓ where
    ∣_∣₀ :  fst C → ∣ C ∣
    ∣_⇒_∋_∣₁ : (x y : fst C) → fst (snd C) x y → ∣ x ∣₀ ≡ ∣ y ∣₀
    ∣_,_,_,_∋_∣₂ : ∀ {a b c d}
      (t : fst (snd C) a b) (bo : fst (snd C) c d)
      (l : fst (snd C) a c) (r : fst (snd C) b d) → snd (snd C) t bo l r
      → PathP (λ i → ∣ a ⇒ c ∋ l ∣₁ i ≡ ∣ b ⇒ d ∋ r ∣₁ i) ∣ a ⇒ b ∋ t ∣₁ ∣ c ⇒ d ∋ bo ∣₁


infix 40 ∣_∣₀
infix 40 ∣_⇒_∋_∣₁
infix 40 ∣_,_,_,_∋_∣₂



import CType1 as GR


-- 2-dimensional CTypes without squares are just 1-dimensional CTypes

noSq : {V : Type ℓ} {E : V → V → Type ℓ} → ∣ V , E , (λ _ _ _ _ → ⊥*) ∣ ≡ GR.∣ V , E ∣
noSq {V = V} {E = E} = isoToPath (iso F G S R) where
  F : ∣ V , E , (λ _ _ _ _ → ⊥*) ∣ → GR.∣ V , E ∣
  F ∣ u ∣₀ = GR.∣ u ∣₀
  F (∣ u ⇒ v ∋ f ∣₁ i) = GR.∣ u ⇒ v ∋ f ∣₁ i
  F (∣ _ , _ , _ , _ ∋ lift () ∣₂ i j)
  G : GR.∣ V , E ∣ → ∣ V , E , (λ _ _ _ _ → ⊥*) ∣
  G GR.∣ u ∣₀ = ∣ u ∣₀
  G (GR.∣ u ⇒ v ∋ f ∣₁ i) = ∣ u ⇒ v ∋ f ∣₁ i
  S : (x : GR.∣ V , E ∣) → F (G x) ≡ x
  S GR.∣ u ∣₀ = refl
  S (GR.∣ u ⇒ v ∋ f ∣₁ i) = refl
  R : (y : ∣ V , E , (λ _ _ _ _ → ⊥*) ∣) → G (F y) ≡ y
  R ∣ u ∣₀ = refl
  R (∣ u ⇒ v ∋ f ∣₁ i) = refl
  R (∣ _ , _ , _ , _ ∋ lift () ∣₂ i j)

