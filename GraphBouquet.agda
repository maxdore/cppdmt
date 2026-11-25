{-# OPTIONS --cubical --guardedness --safe #-}

-- The realisation of a graph with a spanning tree is a bouquet of circles
module GraphBouquet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.Bouquet.Base

open import Prelude using (pqr⁻¹r≡pq)
open import CType1

private
  variable
    ℓ : Level

module _ {V : Type ℓ} (T L : V → V → Type ℓ) where

  -- the edges are the disjoint union of tree and the remaining edges
  E : V → V → Type ℓ
  E u v = T u v ⊎ L u v

  -- one circle for every edge outside the tree
  Loops : Type ℓ
  Loops = Σ[ u ∈ V ] Σ[ v ∈ V ] L u v

  -- the tree sits inside the graph
  ι : ∣ V , T ∣ → ∣ V , E ∣
  ι ∣ v ∣₀ = ∣ v ∣₀
  ι (∣ u ⇒ v ∋ t ∣₁ i) = ∣ u ⇒ v ∋ inl t ∣₁ i

  CycleCollapse :
    (r : V)
    (rootPath : (v : V) → Path (∣ V , T ∣) (∣ r ∣₀) (∣ v ∣₀))
    (Fill : {u v : V} (t : T u v)
      → PathP (λ i → Path (∣ V , T ∣) (∣ r ∣₀) (∣ u ⇒ v ∋ t ∣₁ i)) (rootPath u) (rootPath v))
    →  ∣ V , E ∣ ≡ Bouquet Loops
  CycleCollapse r rootPath Fill = isoToPath (iso to from sec ret) where
    -- a path in the graph
    p : (v : V) → Path (∣ V , E ∣) (∣ r ∣₀) (∣ v ∣₀)
    p v = cong ι (rootPath v)

    to : ∣ V , E ∣ → Bouquet Loops
    to ∣ v ∣₀ = base
    to (∣ u ⇒ v ∋ inl t ∣₁ i) = base
    to (∣ u ⇒ v ∋ inr l ∣₁ i) = loop (u , v , l) i

    from : Bouquet Loops → ∣ V , E ∣
    from base = ∣ r ∣₀
    from (loop (u , v , l) i) =
      (p u ∙∙ ∣ u ⇒ v ∋ inr l ∣₁ ∙∙ sym (p v)) i

    -- `to` is constant on the tree
    toConst : (x : ∣ V , T ∣) → to (ι x) ≡ base
    toConst ∣ v ∣₀ = refl
    toConst (∣ u ⇒ v ∋ t ∣₁ i) = refl

    -- and hence on paths
    trivial : {v : V} (q : Path (∣ V , T ∣) (∣ r ∣₀) (∣ v ∣₀))
      → Path (Path (Bouquet Loops) base base) (cong to (cong ι q)) refl
    trivial q κ i = toConst (q i) κ

    -- refl ∙∙ q ∙∙ refl is q
    ∙∙refl : {x y : Bouquet Loops} (q : x ≡ y) → refl ∙∙ q ∙∙ refl ≡ q
    ∙∙refl q = sym (doubleCompPath-filler refl q refl)

    -- so a circle, run around the graph and contracted again, is itself
    loopEq : (u v : V) (l : L u v)
      → cong to (p u ∙∙ ∣ u ⇒ v ∋ inr l ∣₁ ∙∙ sym (p v))
        ≡ loop (u , v , l)
    loopEq u v l =
        cong-∙∙ to (p u) ∣ u ⇒ v ∋ inr l ∣₁ (sym (p v))
      ∙ (λ κ → trivial (rootPath u) κ
                ∙∙ loop (u , v , l)
                ∙∙ sym (trivial (rootPath v) κ))
      ∙ ∙∙refl (loop (u , v , l))

    sec : (x : Bouquet Loops) → to (from x) ≡ x
    sec base = refl
    sec (loop (u , v , l) i) = λ κ → loopEq u v l κ i

    ret : (y : ∣ V , E ∣) → from (to y) ≡ y
    ret ∣ v ∣₀ = p v
    ret (∣ u ⇒ v ∋ inl t ∣₁ i) = λ j → ι (Fill t i j)
    ret (∣ u ⇒ v ∋ inr l ∣₁ i) =
      pqr⁻¹r≡pq (p u) ∣ u ⇒ v ∋ inr l ∣₁ (p v) i

