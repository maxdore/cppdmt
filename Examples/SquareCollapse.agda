{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- `ComplexMorse.SquareCollapse` on its own: a strip of two squares.
--
--          t₁         t₂
--     p₀ ──────▶ p₁ ──────▶ p₂
--     │          │          │
--  l₀ │   sq₁    │ l₁  sq₂  │ l₂
--     ▼          ▼          ▼
--     q₀ ──────▶ q₁ ──────▶ q₂
--          b₁         b₂
--
-- Six vertices, seven edges, two squares.  The matching is chosen so that
-- *only* the two-dimensional half of a Morse collapse does anything:
--
--   · `ν` matches every square with its **right** edge — sq₁ with l₁ and sq₂
--     with l₂ — so both squares and both of those edges are cancelled;
--   · `μ` is the **identity**, which is a legitimate dimension-zero matching
--     (every vertex is then Critical and its gradient path stands still).  So
--     no vertex and no further edge is cancelled, and the graph `E⁻` that
--     `SquareCollapse` produces is exactly "the complex minus the squares and
--     the edges capping them":
--
--          t₁         t₂
--     p₀ ──────▶ p₁ ──────▶ p₂
--     │
--  l₀ │
--     ▼
--     q₀ ──────▶ q₁ ──────▶ q₂
--          b₁         b₂
--
-- which is the zigzag path  p₂ ◀── p₁ ◀── p₀ ──▶ q₀ ──▶ q₁ ──▶ q₂  —  a tree,
-- so the strip is contractible, as a strip of squares should be.
--
-- The point of taking *two* squares rather than one is the recursion inside
-- the collapse.  `Φ` sends the edge matched with a square to the path around
-- the other three sides, and here the other three sides of sq₂ are t₂, b₂ and
-- l₁ — and l₁ is itself matched, with sq₁.  So the collapse of sq₂ is defined
-- in terms of the collapse of sq₁, and it is `acyclic₁` (well-foundedness of
-- the dimension-one gradient relation, `acc₂` below) that makes that
-- recursion legitimate.  Matching sq₁ with l₁ *and* sq₂ with l₁ would not be
-- a matching at all (`μ̂₁-inj` fails); matching sq₁ with l₁ and sq₂ with l₁'s
-- opposite is what happens here, and it terminates after two steps.
module Examples.SquareCollapse where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary

open import Prelude
import GraphMatching as GM
open GM using (Graph)
import CType1 as GR
open import GraphForest
open import ComplexMatching
open import CType2
open import ComplexMorse

--------------------------------------------------------------------------------
-- The cells

data V : Type where
  p₀ p₁ p₂ q₀ q₁ q₂ : V

data E : V → V → Type where
  t₁ : E p₀ p₁
  t₂ : E p₁ p₂
  b₁ : E q₀ q₁
  b₂ : E q₁ q₂
  l₀ : E p₀ q₀
  l₁ : E p₁ q₁
  l₂ : E p₂ q₂

-- `Sq t bo l r` takes its boundary in the order top, bottom, left, right, so
-- the two squares share the edge l₁: it is the right side of sq₁ and the left
-- side of sq₂.
data Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type where
  sq₁ : Sq t₁ b₁ l₀ l₁
  sq₂ : Sq t₂ b₂ l₁ l₂

open Cells V E Sq

cell₁ cell₂ : Squares
cell₁ = p₀ , p₁ , q₀ , q₁ , t₁ , b₁ , l₀ , l₁ , sq₁
cell₂ = p₁ , p₂ , q₁ , q₂ , t₂ , b₂ , l₁ , l₂ , sq₂

-- the shared edge, twice
_ : ∂ cell₁ rt ≡ ∂ cell₂ lf
_ = refl

--------------------------------------------------------------------------------
-- Vertices are discrete
--
-- A vertex is its position in the list, and `ℕ` is discrete; `fromℕ` is a
-- retraction of `num`, which is all the encode-decode this needs.

num : V → ℕ
num p₀ = 0
num p₁ = 1
num p₂ = 2
num q₀ = 3
num q₁ = 4
num q₂ = 5

fromℕ : ℕ → V
fromℕ 0 = p₀
fromℕ 1 = p₁
fromℕ 2 = p₂
fromℕ 3 = q₀
fromℕ 4 = q₁
fromℕ _ = q₂

fromℕ-num : (v : V) → fromℕ (num v) ≡ v
fromℕ-num p₀ = refl
fromℕ-num p₁ = refl
fromℕ-num p₂ = refl
fromℕ-num q₀ = refl
fromℕ-num q₁ = refl
fromℕ-num q₂ = refl

num-inj : {u v : V} → num u ≡ num v → u ≡ v
num-inj {u} {v} p = sym (fromℕ-num u) ∙ cong fromℕ p ∙ fromℕ-num v

V-discrete : Discrete V
V-discrete u v =
  mapDec num-inj (λ ¬p q → ¬p (cong num q)) (discreteℕ (num u) (num v))

--------------------------------------------------------------------------------
-- … and the complex

E-isIrrefl : (u : V) → ¬ (E u u)
E-isIrrefl u ()

E-isHProp : (u v : V) → isHProp (E u v)
E-isHProp _ _ t₁ t₁ = refl
E-isHProp _ _ t₂ t₂ = refl
E-isHProp _ _ b₁ b₁ = refl
E-isHProp _ _ b₂ b₂ = refl
E-isHProp _ _ l₀ l₀ = refl
E-isHProp _ _ l₁ l₁ = refl
E-isHProp _ _ l₂ l₂ = refl

Sq-isHProp : {a b c d : V} (t : E a b) (bo : E c d) (l : E a c) (r : E b d)
  → isHProp (Sq t bo l r)
Sq-isHProp _ _ _ _ sq₁ sq₁ = refl
Sq-isHProp _ _ _ _ sq₂ sq₂ = refl

-- Non-degeneracy.  Rather than the sixteen cases per square, each square gets
-- a partial inverse of its boundary map — an edge of the strip is a side of a
-- given square in at most one way — and `∂-inj` is the resulting retraction.
sideOf₁ : Edges → Side
sideOf₁ (_ , _ , t₁) = tp
sideOf₁ (_ , _ , b₁) = bt
sideOf₁ (_ , _ , l₀) = lf
sideOf₁ (_ , _ , l₁) = rt
sideOf₁ _ = tp

sideOf₂ : Edges → Side
sideOf₂ (_ , _ , t₂) = tp
sideOf₂ (_ , _ , b₂) = bt
sideOf₂ (_ , _ , l₁) = lf
sideOf₂ (_ , _ , l₂) = rt
sideOf₂ _ = tp

sideOf₁-sec : (i : Side) → sideOf₁ (∂ cell₁ i) ≡ i
sideOf₁-sec tp = refl
sideOf₁-sec bt = refl
sideOf₁-sec lf = refl
sideOf₁-sec rt = refl

sideOf₂-sec : (i : Side) → sideOf₂ (∂ cell₂ i) ≡ i
sideOf₂-sec tp = refl
sideOf₂-sec bt = refl
sideOf₂-sec lf = refl
sideOf₂-sec rt = refl

∂-inj : (s : Squares) {i j : Side} → ∂ s i ≡ ∂ s j → i ≡ j
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , sq₁) {i} {j} p =
  sym (sideOf₁-sec i) ∙ cong sideOf₁ p ∙ sideOf₁-sec j
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , sq₂) {i} {j} p =
  sym (sideOf₂-sec i) ∙ cong sideOf₂ p ∙ sideOf₂-sec j

graph : Graph V E
graph = record
  { V-discrete = V-discrete ; E-isIrrefl = E-isIrrefl ; E-isHProp = E-isHProp }

complex : Complex V E Sq
complex = record { graph = graph ; Sq-isHProp = Sq-isHProp ; ∂-inj = ∂-inj }

open Graph graph using (Edges-discrete)

--------------------------------------------------------------------------------
-- Distinctness, by computation
--
-- Every cell of the strip is a closed term, so `Edges-discrete` *computes* on
-- any two of them; when the answer is `no` the implicit `h` is `⊤` and Agda
-- solves it by η.  This is the `Bool→Type` reflection of `ImageMatching` in
-- miniature, and it discharges every inequality below.

isNo : {A : Type} → Dec A → Type
isNo (yes _) = ⊥
isNo (no _) = ⊤

fromNo : {A : Type} (d : Dec A) → isNo d → ¬ A
fromNo (yes _) ()
fromNo (no ¬a) _ = ¬a

_≠ₑ_ : Edges → Edges → Type
e ≠ₑ f = ¬ (e ≡ f)

E≢ : {e f : Edges} {h : isNo (Edges-discrete e f)} → e ≠ₑ f
E≢ {e} {f} {h} = fromNo (Edges-discrete e f) h

--------------------------------------------------------------------------------
-- The matching
--
--   · `ν` matches every square with its right edge: sq₁ with l₁, sq₂ with l₂;
--   · `μ` is the identity, so every vertex is Critical and dimension zero
--     cancels nothing.
--
-- Being matched upwards is therefore "being the right edge of a square", and
-- `μ̂₁ s ≡ e` unfolds to `∂ s rt ≡ e`, which is what `isUpʳ` spells out.

μ : V → V
μ x = x

ν : Squares → Side
ν _ = rt

isUpʳ : Edges → Type
isUpʳ e = Σ[ s ∈ Squares ] ∂ s rt ≡ e

-- an edge that is neither ∂ cell₁ rt nor ∂ cell₂ rt caps no square
¬up : (e : Edges) → ∂ cell₁ rt ≠ₑ e → ∂ cell₂ rt ≠ₑ e → ¬ isUpʳ e
¬up e h₁ h₂ ((_ , _ , _ , _ , _ , _ , _ , _ , sq₁) , p) = h₁ p
¬up e h₁ h₂ ((_ , _ , _ , _ , _ , _ , _ , _ , sq₂) , p) = h₂ p

¬up-t₁ : ¬ isUpʳ (p₀ , p₁ , t₁)
¬up-t₁ = ¬up _ E≢ E≢
¬up-t₂ : ¬ isUpʳ (p₁ , p₂ , t₂)
¬up-t₂ = ¬up _ E≢ E≢
¬up-b₁ : ¬ isUpʳ (q₀ , q₁ , b₁)
¬up-b₁ = ¬up _ E≢ E≢
¬up-b₂ : ¬ isUpʳ (q₁ , q₂ , b₂)
¬up-b₂ = ¬up _ E≢ E≢
¬up-l₀ : ¬ isUpʳ (p₀ , q₀ , l₀)
¬up-l₀ = ¬up _ E≢ E≢

-- a square is determined by its right edge: the two right edges are distinct
μ̂-inj : {s s' : Squares} → ∂ s rt ≡ ∂ s' rt → s ≡ s'
μ̂-inj {_ , _ , _ , _ , _ , _ , _ , _ , sq₁} {_ , _ , _ , _ , _ , _ , _ , _ , sq₁} p = refl
μ̂-inj {_ , _ , _ , _ , _ , _ , _ , _ , sq₂} {_ , _ , _ , _ , _ , _ , _ , _ , sq₂} p = refl
μ̂-inj {_ , _ , _ , _ , _ , _ , _ , _ , sq₁} {_ , _ , _ , _ , _ , _ , _ , _ , sq₂} p = absurd (E≢ p)
μ̂-inj {_ , _ , _ , _ , _ , _ , _ , _ , sq₂} {_ , _ , _ , _ , _ , _ , _ , _ , sq₁} p = absurd (E≢ p)

-- `μ` is the identity, so no edge is matched downwards at all — that would
-- ask for a loop, and `E` is irreflexive
up∩dn : (e : Edges) → isUpʳ e → ¬ (μ (src e) ≡ tgt e)
up∩dn (u , v , f) _ q = E-isIrrefl u (subst (E u) (sym q) f)

isUp? : (e : Edges) → Dec (isUpʳ e)
isUp? (_ , _ , t₁) = no ¬up-t₁
isUp? (_ , _ , t₂) = no ¬up-t₂
isUp? (_ , _ , b₁) = no ¬up-b₁
isUp? (_ , _ , b₂) = no ¬up-b₂
isUp? (_ , _ , l₀) = no ¬up-l₀
isUp? (_ , _ , l₁) = yes (cell₁ , refl)
isUp? (_ , _ , l₂) = yes (cell₂ , refl)

matchingData : MatchingData complex
matchingData = record
  { μ₀ = μ ; μ₁ = ν ; μ̂₁-inj = μ̂-inj ; up∩dn = up∩dn ; isUp? = isUp? }

open GM.Paths graph μ using (end ; acyclic)
open GradientPaths complex matchingData using (isUp ; _⇒₁_ ; _<₁_ ; acyclic₁ ; upStep)

--------------------------------------------------------------------------------
-- … is acyclic in both dimensions
--
-- Dimension zero is vacuous: `μ` is the identity, so every vertex is already
-- Critical and its gradient path is `end`.

flow : acyclic
flow u = (u , refl) , end refl refl

-- Dimension one is where the two squares interact.  Only l₁ and l₂ are
-- matched upwards, so nothing else can step at all:

accNoUp : (e : Edges) → ¬ isUp e → Acc _<₁_ e
accNoUp e ¬u = acc λ f stp → absurd (¬u (upStep stp))

-- Out of l₁ the only square to leave through is sq₁, whose other three sides
-- are t₁, b₁ and l₀ — none of them matched upwards, so l₁ is accessible after
-- one step.
stepFrom₁ : (f : Edges) → (p₁ , q₁ , l₁) ⇒₁ f → ¬ isUp f
stepFrom₁ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₂) , p , _) = absurd (E≢ p)
stepFrom₁ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₁) , _ , tp , _ , q) =
  subst (λ g → ¬ isUp g) q ¬up-t₁
stepFrom₁ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₁) , _ , bt , _ , q) =
  subst (λ g → ¬ isUp g) q ¬up-b₁
stepFrom₁ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₁) , _ , lf , _ , q) =
  subst (λ g → ¬ isUp g) q ¬up-l₀
stepFrom₁ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₁) , _ , rt , ¬rt , _) =
  absurd (¬rt refl)

acc₁ : Acc _<₁_ (p₁ , q₁ , l₁)
acc₁ = acc λ f stp → accNoUp f (stepFrom₁ f stp)

-- Out of l₂ the square is sq₂, and one of its other three sides is l₁ itself:
-- this is the recursive case, and it is discharged by `acc₁`.
acc₂ : Acc _<₁_ (p₂ , q₂ , l₂)
acc₂ = acc stepFrom₂ where
  stepFrom₂ : (f : Edges) → (p₂ , q₂ , l₂) ⇒₁ f → Acc _<₁_ f
  stepFrom₂ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₁) , p , _) = absurd (E≢ p)
  stepFrom₂ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₂) , _ , tp , _ , q) =
    subst (Acc _<₁_) q (accNoUp _ ¬up-t₂)
  stepFrom₂ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₂) , _ , bt , _ , q) =
    subst (Acc _<₁_) q (accNoUp _ ¬up-b₂)
  stepFrom₂ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₂) , _ , lf , _ , q) =
    subst (Acc _<₁_) q acc₁
  stepFrom₂ f ((_ , _ , _ , _ , _ , _ , _ , _ , sq₂) , _ , rt , ¬rt , _) =
    absurd (¬rt refl)

flow₁ : acyclic₁
flow₁ (_ , _ , t₁) = accNoUp _ ¬up-t₁
flow₁ (_ , _ , t₂) = accNoUp _ ¬up-t₂
flow₁ (_ , _ , b₁) = accNoUp _ ¬up-b₁
flow₁ (_ , _ , b₂) = accNoUp _ ¬up-b₂
flow₁ (_ , _ , l₀) = accNoUp _ ¬up-l₀
flow₁ (_ , _ , l₁) = acc₁
flow₁ (_ , _ , l₂) = acc₂

matching : 2FullMatching complex
matching = matchingData , flow , flow₁

module MS = MorseSquares complex matching

--------------------------------------------------------------------------------
-- The collapse
--
-- `SquareCollapse` cancels both squares and both matched edges, and leaves
-- the vertices and the other five edges alone.

collapse : ∣ V , E , Sq ∣ ≡ ∣ V , MS.E⁻ , (λ _ _ _ _ → ⊥*) ∣
collapse = MS.SquareCollapse

--------------------------------------------------------------------------------
-- What is left: the zigzag
--
-- `MS.E⁻ u v` is an edge of the strip together with a proof that it caps no
-- square, so it is `E` minus l₁ and l₂ — the two edges the squares were
-- matched with, and the only two the collapse removes …

no-l₁ : ¬ MS.E⁻ p₁ q₁
no-l₁ (l₁ , ¬u) = ¬u (cell₁ , refl)

no-l₂ : ¬ MS.E⁻ p₂ q₂
no-l₂ (l₂ , ¬u) = ¬u (cell₂ , refl)

-- … leaving the graph below, on the same six vertices.

data Zig : V → V → Type where
  zt₁ : Zig p₀ p₁
  zt₂ : Zig p₁ p₂
  zb₁ : Zig q₀ q₁
  zb₂ : Zig q₁ q₂
  zl₀ : Zig p₀ q₀

F₁ : (u v : V) → MS.E⁻ u v → Zig u v
F₁ _ _ (t₁ , _) = zt₁
F₁ _ _ (t₂ , _) = zt₂
F₁ _ _ (b₁ , _) = zb₁
F₁ _ _ (b₂ , _) = zb₂
F₁ _ _ (l₀ , _) = zl₀
F₁ _ _ (l₁ , ¬u) = absurd (¬u (cell₁ , refl))
F₁ _ _ (l₂ , ¬u) = absurd (¬u (cell₂ , refl))

G₁ : (u v : V) → Zig u v → MS.E⁻ u v
G₁ _ _ zt₁ = t₁ , ¬up-t₁
G₁ _ _ zt₂ = t₂ , ¬up-t₂
G₁ _ _ zb₁ = b₁ , ¬up-b₁
G₁ _ _ zb₂ = b₂ , ¬up-b₂
G₁ _ _ zl₀ = l₀ , ¬up-l₀

S₁ : (u v : V) (z : Zig u v) → F₁ u v (G₁ u v z) ≡ z
S₁ _ _ zt₁ = refl
S₁ _ _ zt₂ = refl
S₁ _ _ zb₁ = refl
S₁ _ _ zb₂ = refl
S₁ _ _ zl₀ = refl

-- the round trip changes only the `¬ isUp` witness an edge carries, and that
-- is a proposition
R₁ : (u v : V) (f : MS.E⁻ u v) → G₁ u v (F₁ u v f) ≡ f
R₁ _ _ (t₁ , _) = Σ≡Prop (λ _ → isProp¬ _) refl
R₁ _ _ (t₂ , _) = Σ≡Prop (λ _ → isProp¬ _) refl
R₁ _ _ (b₁ , _) = Σ≡Prop (λ _ → isProp¬ _) refl
R₁ _ _ (b₂ , _) = Σ≡Prop (λ _ → isProp¬ _) refl
R₁ _ _ (l₀ , _) = Σ≡Prop (λ _ → isProp¬ _) refl
R₁ _ _ (l₁ , ¬u) = absurd (¬u (cell₁ , refl))
R₁ _ _ (l₂ , ¬u) = absurd (¬u (cell₂ , refl))

∣E⁻∣≡∣Zig∣ : GR.∣ V , MS.E⁻ ∣ ≡ GR.∣ V , Zig ∣
∣E⁻∣≡∣Zig∣ = GR.isoReal (λ u → u) F₁ (λ u → u) G₁
  (λ _ → refl) (λ u v z → S₁ u v z) (λ _ → refl) (λ u v f → R₁ u v f)

-- the strip is the zigzag
strip≡zigzag : ∣ V , E , Sq ∣ ≡ GR.∣ V , Zig ∣
strip≡zigzag = collapse ∙ noSq ∙ ∣E⁻∣≡∣Zig∣

--------------------------------------------------------------------------------
-- … and the zigzag is a point
--
-- The five remaining edges form a tree rooted at p₀ — each vertex's path to
-- the root is the previous one followed by one more edge — so `GraphForest`
-- finishes the collapse, and the strip of two squares is contractible.

zig : {u v : V} → Zig u v → Path (GR.∣ V , Zig ∣) (GR.∣ u ∣₀) (GR.∣ v ∣₀)
zig {u} {v} z = GR.∣ u ⇒ v ∋ z ∣₁

rp₀ : Path (GR.∣ V , Zig ∣) (GR.∣ p₀ ∣₀) (GR.∣ p₀ ∣₀)
rp₀ = refl
rp₁ = rp₀ ∙ zig zt₁
rp₂ = rp₁ ∙ zig zt₂
rq₀ = rp₀ ∙ zig zl₀
rq₁ = rq₀ ∙ zig zb₁
rq₂ = rq₁ ∙ zig zb₂

ι : ⊤ → V
ι tt = p₀

root : V → ⊤
root _ = tt

rootIsRoot : (r : ⊤) → root (ι r) ≡ r
rootIsRoot tt = refl

rootPath : (v : V) → Path (GR.∣ V , Zig ∣) (GR.∣ ι (root v) ∣₀) (GR.∣ v ∣₀)
rootPath p₀ = rp₀
rootPath p₁ = rp₁
rootPath p₂ = rp₂
rootPath q₀ = rq₀
rootPath q₁ = rq₁
rootPath q₂ = rq₂

contrEdge : {u v : V} (z : Zig u v)
  → Σ[ α ∈ root u ≡ root v ]
      PathP (λ i → Path (GR.∣ V , Zig ∣) (GR.∣ ι (α i) ∣₀) (GR.∣ u ⇒ v ∋ z ∣₁ i))
            (rootPath u) (rootPath v)
contrEdge zt₁ = refl , compPath-filler rp₀ (zig zt₁)
contrEdge zt₂ = refl , compPath-filler rp₁ (zig zt₂)
contrEdge zb₁ = refl , compPath-filler rq₀ (zig zb₁)
contrEdge zb₂ = refl , compPath-filler rq₁ (zig zb₂)
contrEdge zl₀ = refl , compPath-filler rp₀ (zig zl₀)

∣Zig∣≡⊤ : GR.∣ V , Zig ∣ ≡ ⊤
∣Zig∣≡⊤ = ForestCollapse ⊤ ι root rootIsRoot rootPath contrEdge

∣strip∣≡⊤ : ∣ V , E , Sq ∣ ≡ ⊤
∣strip∣≡⊤ = strip≡zigzag ∙ ∣Zig∣≡⊤
