{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- Three forests, collapsed by `GraphForest`.
--
-- `Examples.Voevodsky` uses the collapse on a forest that came out of a
-- Morse reduction, and does it by tabulation: 61 vertices, so 61 paths and 59
-- triangles, written out one per line.  Here the same lemma is applied to
-- forests one can look at.  The first is a picture with eight vertices, and is
-- the tabulated proof in miniature.  The other two are infinite — the ray and
-- the complete binary tree — where there is nothing to tabulate and the path
-- from the root to a vertex is defined by recursion on the vertex instead.
--
-- All three are the same four lines of input to `ForestCollapse`: a root for
-- every vertex, the roots hitting themselves, a path from the root of a vertex
-- to it, and a triangle for every edge.  Every triangle is a
-- `compPath-filler`, because every path is its
-- parent's followed by the edge between them.  Which of the two forms is
-- needed depends only on which way the edge points: `compPath-filler` when it
-- points from the parent to the child, and `symP (compPath-filler _ (sym _))`
-- when it points the other way.
module Examples.Trees where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import CType1
open import GraphForest

private
  variable
    ℓ : Level

--------------------------------------------------------------------------------
-- A forest with two components
--
--     a ─── b ─── c ─── e            f ─── g
--           │                        │
--           d                        h
--
-- The edges are directed, and the directions have nothing to do with the tree
-- structure: `c ⇒ b` points from the child to the parent, `a ⇒ b` from the
-- parent to the child.  The realisation does not care — a path is a path — but
-- the triangles below do, and that is the only place it shows.

data Vtx : Type where
  a b c d e f g h : Vtx

data Arr : Vtx → Vtx → Type where
  a⇒b : Arr a b
  c⇒b : Arr c b
  b⇒d : Arr b d
  c⇒e : Arr c e
  f⇒g : Arr f g
  h⇒f : Arr h f

-- the two roots
ι : Bool → Vtx
ι false = a
ι true  = f

-- and the path from the root of a vertex's component to the vertex, running
-- down the tree: each one is its parent's path followed by the edge between
pa : Path (∣ Vtx , Arr ∣) (∣ ι false ∣₀) (∣ a ∣₀)
pa = refl
pb : Path (∣ Vtx , Arr ∣) (∣ ι false ∣₀) (∣ b ∣₀)
pb = pa ∙ ∣ a ⇒ b ∋ a⇒b ∣₁
pc : Path (∣ Vtx , Arr ∣) (∣ ι false ∣₀) (∣ c ∣₀)
pc = pb ∙ sym ∣ c ⇒ b ∋ c⇒b ∣₁
pd : Path (∣ Vtx , Arr ∣) (∣ ι false ∣₀) (∣ d ∣₀)
pd = pb ∙ ∣ b ⇒ d ∋ b⇒d ∣₁
pe : Path (∣ Vtx , Arr ∣) (∣ ι false ∣₀) (∣ e ∣₀)
pe = pc ∙ ∣ c ⇒ e ∋ c⇒e ∣₁
pf : Path (∣ Vtx , Arr ∣) (∣ ι true ∣₀) (∣ f ∣₀)
pf = refl
pg : Path (∣ Vtx , Arr ∣) (∣ ι true ∣₀) (∣ g ∣₀)
pg = pf ∙ ∣ f ⇒ g ∋ f⇒g ∣₁
ph : Path (∣ Vtx , Arr ∣) (∣ ι true ∣₀) (∣ h ∣₀)
ph = pf ∙ sym ∣ h ⇒ f ∋ h⇒f ∣₁

-- which component a vertex lives in
root : Vtx → Bool
root a = false
root b = false
root c = false
root d = false
root e = false
root f = true
root g = true
root h = true

rootIsRoot : (r : Bool) → root (ι r) ≡ r
rootIsRoot false = refl
rootIsRoot true  = refl

rootPath : (v : Vtx) → Path (∣ Vtx , Arr ∣) (∣ ι (root v) ∣₀) (∣ v ∣₀)
rootPath a = pa
rootPath b = pb
rootPath c = pc
rootPath d = pd
rootPath e = pe
rootPath f = pf
rootPath g = pg
rootPath h = ph

contrEdge : {u v : Vtx} (x : Arr u v)
  → Σ[ α ∈ root u ≡ root v ]
      PathP (λ i → Path (∣ Vtx , Arr ∣) (∣ ι (α i) ∣₀) (∣ u ⇒ v ∋ x ∣₁ i))
            (rootPath u) (rootPath v)
contrEdge a⇒b = refl , compPath-filler pa ∣ a ⇒ b ∋ a⇒b ∣₁
contrEdge c⇒b = refl , symP (compPath-filler pb (sym ∣ c ⇒ b ∋ c⇒b ∣₁))
contrEdge b⇒d = refl , compPath-filler pb ∣ b ⇒ d ∋ b⇒d ∣₁
contrEdge c⇒e = refl , compPath-filler pc ∣ c ⇒ e ∋ c⇒e ∣₁
contrEdge f⇒g = refl , compPath-filler pf ∣ f ⇒ g ∋ f⇒g ∣₁
contrEdge h⇒f = refl , symP (compPath-filler pf (sym ∣ h ⇒ f ∋ h⇒f ∣₁))

-- two components, no cycles: `Bool`
∣Arr∣≡Bool : ∣ Vtx , Arr ∣ ≡ Bool
∣Arr∣≡Bool = ForestCollapse Bool ι root rootIsRoot rootPath contrEdge

--------------------------------------------------------------------------------
-- The ray
--
--     0 ◂─── 1 ◂─── 2 ◂─── 3 ◂─── ⋯
--
-- One vertex per natural number and an edge from every number to its
-- predecessor.  There are infinitely many vertices and infinitely many edges,
-- and the whole thing is a point.
--
-- Nothing can be tabulated here, but nothing has to be: the two recursive
-- clauses of `up` are the two lines of the picture above, and the single
-- clause of `contrEdgeℕ` is the triangle spanned by a step and the path
-- leading into it.

data Step : ℕ → ℕ → Type where
  step : (n : ℕ) → Step (suc n) n

zero∙ : Unit → ℕ
zero∙ tt = 0

rootℕ : ℕ → Unit
rootℕ _ = tt

rootℕIsRoot : (r : Unit) → rootℕ (zero∙ r) ≡ r
rootℕIsRoot tt = refl

up : (n : ℕ) → Path (∣ ℕ , Step ∣) (∣ zero∙ (rootℕ n) ∣₀) (∣ n ∣₀)
up zero = refl
up (suc n) = up n ∙ sym ∣ suc n ⇒ n ∋ step n ∣₁

contrEdgeℕ : {u v : ℕ} (x : Step u v)
  → Σ[ α ∈ rootℕ u ≡ rootℕ v ]
      PathP (λ i → Path (∣ ℕ , Step ∣) (∣ zero∙ (α i) ∣₀) (∣ u ⇒ v ∋ x ∣₁ i))
            (up u) (up v)
contrEdgeℕ (step n) = refl , symP (compPath-filler (up n) (sym ∣ suc n ⇒ n ∋ step n ∣₁))

∣Step∣≡Unit : ∣ ℕ , Step ∣ ≡ Unit
∣Step∣≡Unit = ForestCollapse Unit zero∙ rootℕ rootℕIsRoot up contrEdgeℕ

--------------------------------------------------------------------------------
-- A forest of complete binary trees, one for every element of a type
--
--                          (r , [])
--                         ╱        ╲
--                (r , false ∷ [])  (r , true ∷ [])
--                 ╱      ╲            ╱      ╲
--               ⋯          ⋯        ⋯          ⋯
--
-- A vertex is a root `r` together with the address of a node in the tree above
-- it, and every node has an edge to its parent.  Whatever the type of roots,
-- the realisation is that type back again: the trees are infinite, but a tree
-- is a point, so gluing one onto each element of `R` changes nothing.

module Trees (R : Type ℓ) where

  Node : Type ℓ
  Node = R × List Bool

  data Child : Node → Node → Type ℓ where
    child : (r : R) (x : Bool) (xs : List Bool) → Child (r , x ∷ xs) (r , xs)

  ιR : R → Node
  ιR r = r , []

  -- the tree a node lives in is the root it carries
  rootR : Node → R
  rootR = fst

  rootRIsRoot : (r : R) → rootR (ιR r) ≡ r
  rootRIsRoot r = refl

  -- down from the root of the tree the vertex lives in, one edge per letter of
  -- its address
  down : (v : Node) → Path (∣ Node , Child ∣) (∣ ιR (rootR v) ∣₀) (∣ v ∣₀)
  down (r , []) = refl
  down (r , x ∷ xs) = down (r , xs) ∙ sym ∣ (r , x ∷ xs) ⇒ (r , xs) ∋ child r x xs ∣₁

  contrEdgeR : {u v : Node} (x : Child u v)
    → Σ[ α ∈ rootR u ≡ rootR v ]
        PathP (λ i → Path (∣ Node , Child ∣) (∣ ιR (α i) ∣₀) (∣ u ⇒ v ∋ x ∣₁ i))
              (down u) (down v)
  contrEdgeR (child r x xs) = refl ,
    symP (compPath-filler (down (r , xs))
                          (sym ∣ (r , x ∷ xs) ⇒ (r , xs) ∋ child r x xs ∣₁))

  ∣Child∣≡R : ∣ Node , Child ∣ ≡ R
  ∣Child∣≡R = ForestCollapse R ιR rootR rootRIsRoot down contrEdgeR

-- the complete binary tree is a point …
∣binaryTree∣≡Unit : ∣ Trees.Node Unit , Trees.Child Unit ∣ ≡ Unit
∣binaryTree∣≡Unit = Trees.∣Child∣≡R Unit

-- … and two of them are `Bool`, the same answer as the eight-vertex forest
-- above and as the picture in `Examples.Voevodsky`
∣twoBinaryTrees∣≡Bool : ∣ Trees.Node Bool , Trees.Child Bool ∣ ≡ Bool
∣twoBinaryTrees∣≡Bool = Trees.∣Child∣≡R Bool
