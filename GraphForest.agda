{-# OPTIONS --cubical --guardedness --safe #-}

-- The realisation of a rooted forest is its set of roots.

module GraphForest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import CType1

private
  variable
    ℓ : Level

module _ {V : Type ℓ} {E : V → V → Type ℓ} (R : Type ℓ)
  (ι : R → V) (root : V → R) (rootIsRoot : (r : R) → root (ι r) ≡ r)
  where
  ForestCollapse :
    (rootPath : (v : V) → (∣ ι (root v) ∣₀) ≡ (∣ v ∣₀))
    (contrEdge : {u v : V} (e : E u v) → Σ[ α ∈ root u ≡ root v ] PathP (λ i → Path (∣ V , E ∣) (∣ ι (α i) ∣₀) (∣ u ⇒ v ∋ e ∣₁ i)) (rootPath u) (rootPath v))
    → ∣ V , E ∣ ≡ R
  ForestCollapse rootPath contrEdge = isoToPath (iso to from sec ret)
    where
    to : ∣ V , E ∣ → R
    to ∣ v ∣₀ = root v
    to (∣ u ⇒ v ∋ e ∣₁ i) = fst (contrEdge e) i

    from : R → ∣ V , E ∣
    from r = ∣ ι r ∣₀

    sec : (r : R) → to (from r) ≡ r
    sec = rootIsRoot

    ret : (z : ∣ V , E ∣) → from (to z) ≡ z
    ret ∣ v ∣₀ = rootPath v
    ret (∣ u ⇒ v ∋ e ∣₁ i) = snd (contrEdge e) i

