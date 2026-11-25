{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- Three graphs with cycles, collapsed by `GraphBouquet`.
--
-- `Examples.Mug` uses the collapse on the graph that came out of a Morse
-- reduction; here the same lemma is applied to graphs one can look at.  The
-- input is the input of `Examples.Trees` for the tree part alone — a root, a
-- path down the tree to every vertex, and a triangle for every tree edge — and
-- the edges left over come out as circles.
module Examples.Bouquets where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.HITs.S1
open import Cubical.HITs.Wedge

open import CType1
import GraphBouquet as GB

--------------------------------------------------------------------------------
-- The circle
--
--     ⋆ ⟲
--
-- One vertex, no tree edges and one loop.  The tree is a point, so the path
-- from the root to the only vertex is `refl` and there is no triangle to give.

data ⋆₀ : Type where
  ⋆ : ⋆₀

data NoEdge : ⋆₀ → ⋆₀ → Type where

data Self : ⋆₀ → ⋆₀ → Type where
  self : Self ⋆ ⋆

P⋆ : (v : ⋆₀) → Path (∣ ⋆₀ , NoEdge ∣) (∣ ⋆ ∣₀) (∣ v ∣₀)
P⋆ ⋆ = refl

Fill⋆ : {u v : ⋆₀} (t : NoEdge u v)
  → PathP (λ i → Path (∣ ⋆₀ , NoEdge ∣) (∣ ⋆ ∣₀) (∣ u ⇒ v ∋ t ∣₁ i)) (P⋆ u) (P⋆ v)
Fill⋆ ()

-- one edge outside the tree, so one circle
∣Self∣≡S¹ : ∣ ⋆₀ , (λ u v → NoEdge u v ⊎ Self u v) ∣ ≡ S¹
∣Self∣≡S¹ = GB.CycleCollapse NoEdge Self ⋆ P⋆ Fill⋆
  ∙ sym ∣pt∣≡Bouquet
  ∙ isoReal (λ _ → tt)  (λ _ _ _ → tt)
            (λ _ → tt*) (λ _ _ _ → ⋆ , ⋆ , self)
            (λ _ → refl) (λ _ _ _ → refl)
            (λ _ → refl) (λ { _ _ (_ , _ , self) → refl })
  ∙ sym S¹≡∣⊤₁∣

--------------------------------------------------------------------------------
-- Two vertices joined by three edges
--
--             ───
--     a ═══ b ───     (one of the three edges is the tree, the other two
--             ───      are the circles)
--
-- The theta graph: a spanning tree of one edge and two edges left over, which
-- is the shape the mug's Morse complex has as well.

data Vtx : Type where
  a b : Vtx

data Edge : Vtx → Vtx → Type where
  a⇒b : Edge a b

data Rest : Vtx → Vtx → Type where
  r₀ r₁ : Rest a b

Pθ : (v : Vtx) → Path (∣ Vtx , Edge ∣) (∣ a ∣₀) (∣ v ∣₀)
Pθ a = refl
Pθ b = refl ∙ ∣ a ⇒ b ∋ a⇒b ∣₁

Fillθ : {u v : Vtx} (t : Edge u v)
  → PathP (λ i → Path (∣ Vtx , Edge ∣) (∣ a ∣₀) (∣ u ⇒ v ∋ t ∣₁ i)) (Pθ u) (Pθ v)
Fillθ a⇒b = compPath-filler refl ∣ a ⇒ b ∋ a⇒b ∣₁

-- two edges outside the tree, so two circles
∣θ∣≡S¹VS¹ : ∣ Vtx , (λ u v → Edge u v ⊎ Rest u v) ∣ ≡ S¹∙ ⋁ S¹∙
∣θ∣≡S¹VS¹ = GB.CycleCollapse Edge Rest a Pθ Fillθ
  ∙ sym ∣pt∣≡Bouquet
  ∙ isoReal (λ _ → tt)  (λ { _ _ (_ , _ , r₀) → false ; _ _ (_ , _ , r₁) → true })
            (λ _ → tt*) (λ { _ _ false → a , b , r₀ ; _ _ true → a , b , r₁ })
            (λ _ → refl) (λ { _ _ false → refl ; _ _ true → refl })
            (λ _ → refl) (λ { _ _ (_ , _ , r₀) → refl ; _ _ (_ , _ , r₁) → refl })
  ∙ sym S¹VS¹≡∣Bool₁∣

