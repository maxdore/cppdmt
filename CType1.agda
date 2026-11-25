{-# OPTIONS --cubical --guardedness --safe #-}
module CType1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.HITs.S1
open import Cubical.HITs.Wedge
open import Cubical.HITs.Pushout
open import Cubical.HITs.Bouquet.Base

open import Prelude

private
  variable
    ℓ : Level

CType¹ : Type (ℓ-suc ℓ)
CType¹ {ℓ} = Σ[ A ∈ Type ℓ ] (A → A → Type ℓ)

data ∣_∣ (Q : CType¹ {ℓ}) : Type ℓ where
  ∣_∣₀ :  fst Q → ∣ Q ∣
  ∣_⇒_∋_∣₁ : (x y : fst Q) → snd Q x y → ∣ x ∣₀ ≡ ∣ y ∣₀

infix 40 ∣_∣₀
infix 40 ∣_⇒_∋_∣₁


-- Some example semi-cubical types

⊥₁ : ⊤ → ⊤ → Type
⊥₁ tt tt = ⊥

⊤≡∣⊥₁∣ : ⊤ ≡ ∣ ⊤ , ⊥₁ ∣
⊤≡∣⊥₁∣ = isoToPath (iso (λ _ → ∣ tt ∣₀) (λ _ → tt)
  (λ {∣ tt ∣₀ → refl ; (∣ tt ⇒ tt ∋ () ∣₁ i) }) (λ _ → refl))

-- A single vertex with a family `A` of edges on it is the bouquet of `A`
-- circles: the two are the same data written twice, a point and a loop for
-- every element of `A`.
∣pt∣≡Bouquet : {A : Type ℓ} → ∣ Unit* {ℓ} , (λ _ _ → A) ∣ ≡ Bouquet A
∣pt∣≡Bouquet {A = A} = isoToPath (iso F G S R) where
  F : ∣ Unit* , (λ _ _ → A) ∣ → Bouquet A
  F (∣ tt* ∣₀) = base
  F (∣ tt* ⇒ tt* ∋ a ∣₁ i) = loop a i
  G : Bouquet A → ∣ Unit* , (λ _ _ → A) ∣
  G base = ∣ tt* ∣₀
  G (loop a i) = ∣ tt* ⇒ tt* ∋ a ∣₁ i
  S : (x : Bouquet A) → F (G x) ≡ x
  S base = refl
  S (loop a i) = refl
  R : (y : ∣ Unit* , (λ _ _ → A) ∣) → G (F y) ≡ y
  R (∣ tt* ∣₀) = refl
  R (∣ tt* ⇒ tt* ∋ a ∣₁ i) = refl

⊤₁ : ⊤ → ⊤ → Type
⊤₁ tt tt = ⊤

S¹≡∣⊤₁∣ : S¹ ≡ ∣ ⊤ , ⊤₁ ∣
S¹≡∣⊤₁∣ = isoToPath (iso F G S R) where
  F : S¹ → ∣ ⊤ , ⊤₁ ∣
  F base = ∣ tt ∣₀
  F (loop i) = ∣ tt ⇒ tt ∋ tt ∣₁ i
  G : ∣ ⊤ , ⊤₁ ∣ → S¹
  G (∣ tt ∣₀) = base
  G (∣ tt ⇒ tt ∋ tt ∣₁ i) = loop i
  S : (x : ∣ ⊤ , ⊤₁ ∣) → F (G x) ≡ x
  S (∣ tt ∣₀) = refl
  S (∣ tt ⇒ tt ∋ tt ∣₁ i) = refl
  R : (y : S¹) → G (F y) ≡ y
  R base = refl
  R (loop i) = refl

Bool₁ : ⊤ → ⊤ → Type
Bool₁ tt tt = Bool

S¹∙ : Σ[ A ∈ Type ] A
S¹∙ = S¹ , base

S¹VS¹≡∣Bool₁∣ : S¹∙ ⋁ S¹∙ ≡ ∣ ⊤ , Bool₁ ∣
S¹VS¹≡∣Bool₁∣ = isoToPath (iso F G S R) where
  F : S¹∙ ⋁ S¹∙ → ∣ ⊤ , Bool₁ ∣
  F (inl base) = ∣ tt ∣₀
  F (inl (loop i)) = ∣ tt ⇒ tt ∋ false ∣₁ i
  F (inr base) = ∣ tt ∣₀
  F (inr (loop i)) = ∣ tt ⇒ tt ∋ true  ∣₁ i
  F (push tt i) = ∣ tt ∣₀
  G : ∣ ⊤ , Bool₁ ∣ → S¹∙ ⋁ S¹∙
  G (∣ tt ∣₀) = inl base
  G (∣ tt ⇒ tt ∋ false ∣₁ i) = inl (loop i)
  G (∣ tt ⇒ tt ∋ true ∣₁ i) =
    (push tt ∙∙ (λ j → inr (loop j)) ∙∙ sym (push tt)) i
  R : (y : S¹∙ ⋁ S¹∙) → G (F y) ≡ y
  R (inl base) = refl
  R (inl (loop i)) = refl
  R (inr base) = push tt
  R (inr (loop j)) i = hcomp (λ k → λ {
        (i = i1) → inr (loop j)
      ; (j = i0) → push tt (i ∨ ~ k)
      ; (j = i1) → push tt (i ∨ ~ k)
      }) (inr (loop j))
  R (push tt i) j = push tt (i ∧ j)
  S : (x : ∣ ⊤ , Bool₁ ∣) → F (G x) ≡ x
  S (∣ tt ∣₀) = refl
  S (∣ tt ⇒ tt ∋ false  ∣₁ i) = refl
  S (∣ tt ⇒ tt ∋ true  ∣₁ i) j = computeTransports j i where
    computeTransports : Path (∣ tt ∣₀ ≡ ∣ tt ∣₀)
      ((λ _ → ∣ tt ∣₀) ∙∙
      (λ l → (transp (λ _ → ∣ ⊤ , Bool₁ ∣) i0 (∣ tt ⇒ tt ∋ true  ∣₁ l))) ∙∙
      (λ _ → ∣ tt ∣₀))
      (λ i → ∣ tt ⇒ tt ∋ true  ∣₁ i)
    computeTransports i j = hcomp (λ k → (λ {
        (i = i1) → ∣ tt ⇒ tt ∋ true  ∣₁ j
      ; (j = i0) → ∣ tt ∣₀
      ; (j = i1) → ∣ tt ∣₀
      })) (transportRefl (∣ tt ⇒ tt ∋ true  ∣₁ j) i)

module _ {c₀ : Type ℓ} {c₁ : c₀ → c₀ → Type ℓ}
         {c₀' : Type ℓ} {c₁' : c₀' → c₀' → Type ℓ}
  (F : c₀ → c₀') (F₁ : (x y : c₀) → c₁ x y → c₁' (F x) (F y))
  (G : c₀' → c₀) (G₁ : (x y : c₀') → c₁' x y → c₁ (G x) (G y))
  (S : (x : c₀') → F (G x) ≡ x) (S₁ : (x y : c₀') (f : c₁' x y)
    → PathP (λ i → c₁' (S x i) (S y i)) (F₁ (G x) (G y) (G₁ x y f)) f)
  (R : (x : c₀) → G (F x) ≡ x) (R₁ : (x y : c₀) (f : c₁ x y)
    → PathP (λ i → c₁ (R x i) (R y i)) (G₁ (F x) (F y) (F₁ x y f)) f)
  where
  isoReal : ∣ c₀ , c₁ ∣ ≡ ∣ c₀' , c₁' ∣
  isoReal = isoToPath (iso 𝓕 𝓖 𝓢 𝓡) where
    𝓕 : ∣ c₀ , c₁ ∣ → ∣ c₀' , c₁' ∣
    𝓕 (∣ x ∣₀) = ∣ F x ∣₀
    𝓕 (∣ u ⇒ v ∋ f  ∣₁ i) = ∣ F u ⇒ F v ∋ F₁ u v f ∣₁ i
    𝓖 : ∣ c₀' , c₁' ∣ → ∣ c₀ , c₁ ∣
    𝓖 (∣ x ∣₀) = ∣ G x ∣₀
    𝓖 (∣ u ⇒ v ∋ f  ∣₁ i) = ∣ G u ⇒ G v ∋ G₁ u v f ∣₁ i
    𝓢 : section 𝓕 𝓖
    𝓢 (∣ x ∣₀) = cong ∣_∣₀ (S x)
    𝓢 (∣ u ⇒ v ∋ f  ∣₁ i) j = ∣ S u j ⇒ S v j ∋ S₁ u v f j ∣₁ i
    𝓡 : retract 𝓕 𝓖
    𝓡 (∣ x ∣₀) = cong ∣_∣₀ (R x)
    𝓡 (∣ u ⇒ v ∋ f  ∣₁ i) j = ∣ R u j ⇒ R v j ∋ R₁ u v f j ∣₁ i

