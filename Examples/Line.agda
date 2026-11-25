{-# OPTIONS --cubical --guardedness --safe #-}

-- The line: one vertex per natural number, one edge from every number to its
-- predecessor.  Infinitely many cells, no cycles, hence a point.
--
--     0 ◂─── 1 ◂─── 2 ◂─── 3 ◂─── ⋯
--
-- The line is a tree rooted at `zero`, so the contractibility is `GraphForest`
-- and not the Morse theorem: nothing has to be matched away first.  The two
-- clauses of `down` are the two lines of the picture — the path from the root
-- to `suc n` is the path to `n` followed backwards along the edge between them
-- — and the single triangle is the `compPath-filler` of that composition.
--
-- Note that the edge relation is a path type, `line₁ (suc m) n = m ≡ n`, and
-- not a family of constructors as in `Examples.Trees`; so the triangle is given
-- by `J` on the edge rather than by pattern matching on it.
module Examples.Line where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Relation.Nullary

open import Prelude
open import GraphMatching
open import CType1
open import GraphForest

line₁ : ℕ → ℕ → Type
line₁ zero n = ⊥
line₁ (suc m) n = m ≡ n

line : Graph ℕ line₁
Graph.V-discrete line = discreteℕ
Graph.E-isIrrefl line zero a = a
Graph.E-isIrrefl line (suc m) a = ¬m<m (0 , sym a)
Graph.E-isHProp line zero n = isHProp⊥
Graph.E-isHProp line (suc m) n = isSetℕ m n

line₁? : (u v : ℕ) → Dec (line₁ u v)
line₁? zero n = no (λ p → p)
line₁? (suc m) n = discreteℕ m n


-- the single root, `zero`
ι : ⊤ → ℕ
ι tt = zero

root : ℕ → ⊤
root _ = tt

rootIsRoot : (r : ⊤) → root (ι r) ≡ r
rootIsRoot tt = refl

-- down the line from the root, one edge per `suc`
down : (n : ℕ) → Path (∣ ℕ , line₁ ∣) (∣ ι (root n) ∣₀) (∣ n ∣₀)
down zero = refl
down (suc n) = down n ∙ sym ∣ suc n ⇒ n ∋ refl ∣₁

-- an edge out of `zero` is absurd, and an edge out of `suc m` goes to `m`
contrEdge : {u v : ℕ} (e : line₁ u v)
  → Σ[ α ∈ root u ≡ root v ]
      PathP (λ i → Path (∣ ℕ , line₁ ∣) (∣ ι (α i) ∣₀) (∣ u ⇒ v ∋ e ∣₁ i))
            (down u) (down v)
contrEdge {zero} e = absurd e
contrEdge {suc m} e = refl , J
  (λ w (f : line₁ (suc m) w)
    → PathP (λ i → Path (∣ ℕ , line₁ ∣) (∣ zero ∣₀) (∣ suc m ⇒ w ∋ f ∣₁ i))
            (down (suc m)) (down w))
  (symP (compPath-filler (down m) (sym ∣ suc m ⇒ m ∋ refl ∣₁)))
  e

∣line₁∣≡⊤ : ∣ ℕ , line₁ ∣ ≡ ⊤
∣line₁∣≡⊤ = ForestCollapse ⊤ ι root rootIsRoot down contrEdge

line-isContr : isContr ∣ ℕ , line₁ ∣
line-isContr = subst isContr (sym ∣line₁∣≡⊤) isContrUnit
