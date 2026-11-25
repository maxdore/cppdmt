{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- The torus as a 2-dimensional complex: one vertex, two edges, and a single
-- square gluing them.  Its realisation is the library's torus, with both
-- round-trips holding by `refl` — the two HITs have the same cells.
module Examples.Torus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.HITs.Torus

open import CType2

data TE : Unit → Unit → Type where
  ⟳ ⟲ : TE tt tt

-- the one square has top = bottom = ⟳ and left = right = ⟲
data TSq : {a b c d : Unit} → TE a b → TE c d → TE a c → TE b d → Type where
  glue2 : TSq ⟳ ⟳ ⟲ ⟲

T : Type
T = ∣ Unit , TE , TSq ∣

-- the library's `square : PathP (λ i → line1 i ≡ line1 i) line2 line2` is
-- `Square line2 line2 line1 line1`, so ⟳ is line2 and ⟲ is line1
toT : T → Torus
toT ∣ tt ∣₀ = point
toT (∣ tt ⇒ tt ∋ ⟳ ∣₁ i) = line2 i
toT (∣ tt ⇒ tt ∋ ⟲ ∣₁ i) = line1 i
toT (∣ ⟳ , ⟳ , ⟲ , ⟲ ∋ glue2 ∣₂ i j) = square i j

frT : Torus → T
frT point = ∣ tt ∣₀
frT (line1 i) = ∣ tt ⇒ tt ∋ ⟲ ∣₁ i
frT (line2 i) = ∣ tt ⇒ tt ∋ ⟳ ∣₁ i
frT (square i j) = ∣ ⟳ , ⟳ , ⟲ , ⟲ ∋ glue2 ∣₂ i j

toT-frT : (x : Torus) → toT (frT x) ≡ x
toT-frT point = refl
toT-frT (line1 i) = refl
toT-frT (line2 i) = refl
toT-frT (square i j) = refl

frT-toT : (x : T) → frT (toT x) ≡ x
frT-toT ∣ tt ∣₀ = refl
frT-toT (∣ tt ⇒ tt ∋ ⟳ ∣₁ i) = refl
frT-toT (∣ tt ⇒ tt ∋ ⟲ ∣₁ i) = refl
frT-toT (∣ ⟳ , ⟳ , ⟲ , ⟲ ∋ glue2 ∣₂ i j) = refl

T≡Torus : T ≡ Torus
T≡Torus = isoToPath (iso toT frT toT-frT frT-toT)
