{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- The picture of `Examples.Mug` is a bouquet of two circles.
--
-- The mug has two holes — the one the cup encloses and the one inside the
-- handle — and the Morse theorem of `ComplexMorse` finds them: the complex of the
-- 29×22 bitmap has 328 vertices, 570 edges and 241 squares, but only 6
-- Critical vertices and 7 Critical edges, and that graph is a spanning tree of
-- 5 edges with 2 edges left over.  Each of the two runs parallel to a tree
-- edge — `a4` to `a1` and `a6` to `a0` — so the graph is
--
--     v0 ◂─a2─ v1 ◂─a3─ v2 ◂─a1─ v3 ◂─a5─ v4 ◂─a0─ v5
--                          ╰─a4─╯            ╰─a6─╯
--
-- and each of the two doubled edges is a cycle: the top of the mug's hole with
-- its bottom, and the top of the handle's hole with its bottom.
-- `GraphBouquet` then collapses the tree and leaves the two circles, exactly
-- as `GraphForest` collapsed the forest of `Examples.Voevodsky` and left
-- its two points.
--
-- As there, the picture enters in three ways only: two boolean computations
-- over the whole bitmap (`eBox` and `vBox`) saying that the lists below leave
-- no Critical cell out, and the tables themselves, each entry checked by
-- `refl`.
module Examples.Mug where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.HITs.Wedge
open import Cubical.HITs.Bouquet.Base
open import Agda.Builtin.String

open import CType2
import CType1 as GR
import GraphBouquet as GB
open import ImageMatching
open import ImageMorse

mug : List String
mug =
  "    ###############          " ∷
  "  ###################        " ∷
  " #####################       " ∷
  " #####################       " ∷
  " #####################       " ∷
  " ##                 ##       " ∷
  " ##                 ##       " ∷
  " ##                 #####    " ∷
  " ##                 #######  " ∷
  " ##                 ##  #### " ∷
  " ##                 ##   ### " ∷
  " ##                 ##   ### " ∷
  " ##                 ##   ### " ∷
  " ##                 ##  #### " ∷
  " ##                 #######  " ∷
  " ##                 #####    " ∷
  " ##                 ##       " ∷
  " ##                 ##       " ∷
  " ##                 ##       " ∷
  " #####################       " ∷
  "  ###################        " ∷
  "    ###############          " ∷ []

open Forest mug

--------------------------------------------------------------------------------
-- The Morse complex, written out
--
-- One constructor per Critical vertex, and one per Critical edge — split into
-- the five that form a spanning tree and the two that do not.  `a4` is
-- parallel to `a1` and `a6` to `a0`, so unlike in a forest the endpoints no
-- longer determine an edge.

data Vtx : Type where
  v0 v1 v2 v3 v4 v5 : Vtx

-- the spanning tree: the path  v0 ◂── v1 ◂── v2 ◂── v3 ◂── v4 ◂── v5
data Tree : Vtx → Vtx → Type where
  a0 : Tree v5 v4
  a1 : Tree v3 v2
  a2 : Tree v1 v0
  a3 : Tree v2 v1
  a5 : Tree v4 v3

-- and the two edges it leaves out, one per hole of the mug
data Loop : Vtx → Vtx → Type where
  a4 : Loop v3 v2
  a6 : Loop v5 v4

Arr : Vtx → Vtx → Type
Arr u v = Tree u v ⊎ Loop u v

--------------------------------------------------------------------------------
-- It is a tree with two edges left over, and its realisation is therefore a
-- bouquet of two circles
--
-- The path from the root to a vertex runs *inside the tree*, and is its
-- parent's followed by the edge between them; every tree edge points from the
-- child to the parent, so every triangle is the `symP (compPath-filler _ (sym
-- _))` of `Examples.Trees`.

q0 : Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ v0 ∣₀)
q0 = refl
q1 : Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ v1 ∣₀)
q1 = q0 ∙ sym GR.∣ v1 ⇒ v0 ∋ a2 ∣₁
q2 : Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ v2 ∣₀)
q2 = q1 ∙ sym GR.∣ v2 ⇒ v1 ∋ a3 ∣₁
q3 : Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ v3 ∣₀)
q3 = q2 ∙ sym GR.∣ v3 ⇒ v2 ∋ a1 ∣₁
q4 : Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ v4 ∣₀)
q4 = q3 ∙ sym GR.∣ v4 ⇒ v3 ∋ a5 ∣₁
q5 : Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ v5 ∣₀)
q5 = q4 ∙ sym GR.∣ v5 ⇒ v4 ∋ a0 ∣₁

P : (v : Vtx) → Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ v ∣₀)
P v0 = q0
P v1 = q1
P v2 = q2
P v3 = q3
P v4 = q4
P v5 = q5

Fill : {u v : Vtx} (t : Tree u v)
  → PathP (λ i → Path (GR.∣ Vtx , Tree ∣) (GR.∣ v0 ∣₀) (GR.∣ u ⇒ v ∋ t ∣₁ i)) (P u) (P v)
Fill a2 = symP (compPath-filler q0 (sym GR.∣ v1 ⇒ v0 ∋ a2 ∣₁))
Fill a3 = symP (compPath-filler q1 (sym GR.∣ v2 ⇒ v1 ∋ a3 ∣₁))
Fill a1 = symP (compPath-filler q2 (sym GR.∣ v3 ⇒ v2 ∋ a1 ∣₁))
Fill a5 = symP (compPath-filler q3 (sym GR.∣ v4 ⇒ v3 ∋ a5 ∣₁))
Fill a0 = symP (compPath-filler q4 (sym GR.∣ v5 ⇒ v4 ∋ a0 ∣₁))

∣Arr∣≡Bouquet : GR.∣ Vtx , Arr ∣ ≡ Bouquet (GB.Loops Tree Loop)
∣Arr∣≡Bouquet = GB.CycleCollapse Tree Loop v0 P Fill

-- The bouquet has one circle per edge outside the tree, so two: `GraphRealisation`
-- identifies the graph with one vertex and two loops with `S¹ ∨ S¹`.
loops→Bool : GB.Loops Tree Loop → Bool
loops→Bool (_ , _ , a4) = false
loops→Bool (_ , _ , a6) = true

Bool→loops : Bool → GB.Loops Tree Loop
Bool→loops false = v3 , v2 , a4
Bool→loops true  = v5 , v4 , a6

-- The two are inverse — a loop is determined by which of `a4`, `a6` it is — so
-- the index of the bouquet is `Bool`.
Loops≡Bool : GB.Loops Tree Loop ≡ Bool
Loops≡Bool = isoToPath (iso loops→Bool Bool→loops
  (λ { false → refl ; true → refl })
  (λ { (_ , _ , a4) → refl ; (_ , _ , a6) → refl }))


--------------------------------------------------------------------------------
-- … and it is the Morse complex of the picture
--
-- `G` sends a vertex of the graph above to the Critical vertex it names — the
-- sink of the gradient flow at that position — and `F` looks a position up in
-- the table.  Every clause of `S` is a `refl`: the flow computes.

CritAt : (x y : ℕ) {h : Bool→Type (vertexB x y)} → Mo.Crit₀
CritAt x y {h} = Mo.sink ((x , y) , h)

G : Vtx → Mo.Crit₀
G v0 = CritAt 28 14
G v1 = CritAt 27 15
G v2 = CritAt 25 16
G v3 = CritAt 22 20
G v4 = CritAt 21 21
G v5 = CritAt 19 22

vtxTable : List ((ℕ × ℕ) × Vtx)
vtxTable =
      ((28 , 14) , v0)
    ∷ ((27 , 15) , v1)
    ∷ ((25 , 16) , v2)
    ∷ ((22 , 20) , v3)
    ∷ ((21 , 21) , v4)
    ∷ ((19 , 22) , v5)
  ∷ []

lookupVtx : ℕ → ℕ → List ((ℕ × ℕ) × Vtx) → Vtx
lookupVtx x y []                  = v0
lookupVtx x y (((a , b) , w) ∷ t) =
  if (eqℕ x a and eqℕ y b) then w else lookupVtx x y t

F : Mo.Crit₀ → Vtx
F c = lookupVtx (fst (pos (c Mo.ᵥ))) (snd (pos (c Mo.ᵥ))) vtxTable

S : (v : Vtx) → F (G v) ≡ v
S v0 = refl
S v1 = refl
S v2 = refl
S v3 = refl
S v4 = refl
S v5 = refl

G₁ : (i j : Vtx) → Arr i j → Mo⁻.Crit₁ (G i) (G j)
G₁ v5 v4 (inl a0) = arrAt 3 5
G₁ v3 v2 (inl a1) = arrAt 22 9
G₁ v1 v0 (inl a2) = arrAt 27 14
G₁ v2 v1 (inl a3) = arrAt 25 15
G₁ v3 v2 (inr a4) = arrAt 22 16
G₁ v4 v3 (inl a5) = arrAt 21 20
G₁ v5 v4 (inr a6) = arrAt 19 21

--------------------------------------------------------------------------------
-- Nothing is missing
--
-- A Critical edge of the picture is horizontal, with a white pixel below it
-- and a black one to its south-west; a Critical vertex has neither an edge
-- below it nor a free edge to its right.  Both are boolean conditions, so a
-- single computation over the box the picture lives in checks that the lists
-- below catch every one of them.

CritEdgesB CritVB : ℕ → ℕ → Bool
CritEdgesB x y = hEdgesB x y and (not (black x y) and vEdgesB x y)
CritVB   x y = not (vEdgesB x y) and not (hEdgesB x y and not (black x y))

eList : List (ℕ × ℕ)
eList =
      (3 , 5)
    ∷ (22 , 9)
    ∷ (27 , 14)
    ∷ (25 , 15)
    ∷ (22 , 16)
    ∷ (21 , 20)
    ∷ (19 , 21)
  ∷ []

vList : List (ℕ × ℕ)
vList =
      (28 , 14)
    ∷ (27 , 15)
    ∷ (25 , 16)
    ∷ (22 , 20)
    ∷ (21 , 21)
    ∷ (19 , 22)
  ∷ []

eBox : (u : V) → Bool→Type (not (CritEdgesB (fst (pos u)) (snd (pos u)))
                            or memB (fst (pos u)) (snd (pos u)) eList)
eBox = allVertices (λ x y → not (CritEdgesB x y) or memB x y eList) tt

vBox : (u : V) → Bool→Type (not (CritVB (fst (pos u)) (snd (pos u)))
                            or memB (fst (pos u)) (snd (pos u)) vList)
vBox = allVertices (λ x y → not (CritVB x y) or memB x y vList) tt

eMem : {c d : Mo.Crit₀} (f : Mo⁻.Crit₁ c d)
  → Bool→Type (memB (fst (pos (src (fst f Mo.ₑ)))) (snd (pos (src (fst f Mo.ₑ)))) eList)
eMem ((((x , y) , hu) , v , g , ¬up) , ¬dn , _ , _)
  with CritEdges (((x , y) , hu) , v , g) ¬dn ¬up
... | (h , r , ¬b , vd)
  with or-elim (not (CritEdgesB x y)) (memB x y eList) (eBox ((x , y) , hu))
...   | inl ¬ce = absurd (not-elim (CritEdgesB x y) ¬ce
                    (and-i (hEdgesB x y) (not (black x y) and vEdgesB x y) r
                      (and-i (not (black x y)) (vEdgesB x y) (not-i (black x y) ¬b) vd)))
...   | inr m   = m

vMem : (c : Mo.Crit₀)
  → Bool→Type (memB (fst (pos (c Mo.ᵥ))) (snd (pos (c Mo.ᵥ))) vList)
vMem (((x , y) , hu) , p) with CritVertex ((x , y) , hu) p
... | (¬d , f)
  with or-elim (not (CritVB x y)) (memB x y vList) (vBox ((x , y) , hu))
...   | inl ¬cv = absurd (not-elim (CritVB x y) ¬cv
                    (and-i (not (vEdgesB x y)) (not (hEdgesB x y and not (black x y)))
                      (not-i (vEdgesB x y) ¬d)
                      (not-i (hEdgesB x y and not (black x y))
                        (λ h → not-elim (black x y)
                                 (and-r (hEdgesB x y) (not (black x y)) h)
                                 (f (and-l (hEdgesB x y) (not (black x y)) h))))))
...   | inr m   = m

--------------------------------------------------------------------------------
-- Every cell of the Morse complex is one of the table's
--
-- `edgeIs` identifies an arbitrary edge with the one at its position, and the
-- table entry says which arrow of the graph that is; `vF` does the same for
-- vertices.  The two `refl`s at every call site are the computations that tie
-- the table to the picture.

EFact : ℕ → ℕ → Type
EFact x y = {c d : Mo.Crit₀} (f : Mo⁻.Crit₁ c d) → pos (src (fst f Mo.ₑ)) ≡ (x , y)
          → Σ[ a ∈ Arr (F c) (F d) ] (arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))

eF : (x y : ℕ)
     {hu : Bool→Type (vertexB x y)} {hv : Bool→Type (vertexB (suc x) y)}
     {he : Bool→Type (hEdgesB x y)} {nb : Bool→Type (not (black x y))}
     {vd : Bool→Type (vEdgesB x y)} {hd : Bool→Type (vertexB x (suc y))}
     (a₀ : Arr (F (srcSink x y {hu})) (F (tgtSink x y {hv})))
   → arrow (srcSink x y {hu}) (tgtSink x y {hv}) (arrAt x y {hu} {hv} {he} {nb} {vd} {hd})
       ≡ arrow (G (F (srcSink x y {hu}))) (G (F (tgtSink x y {hv})))
               (G₁ (F (srcSink x y {hu})) (F (tgtSink x y {hv})) a₀)
   → EFact x y
eF x y a₀ e {c} {d} f h =
  subst2 (λ i j → Σ[ a ∈ Arr i j ] (arrow c d f ≡ arrow (G i) (G j) (G₁ i j a)))
    (sym (cong F (cong fst β))) (sym (cong F (cong (λ z → fst (snd z)) β)))
    (a₀ , β ∙ e)
  where β = edgeIs x y f h

eFacts : AllPos {P = EFact} eList
eFacts =
      eF 3 5 (inl a0) refl
    ∷ eF 22 9 (inl a1) refl
    ∷ eF 27 14 (inl a2) refl
    ∷ eF 25 15 (inl a3) refl
    ∷ eF 22 16 (inr a4) refl
    ∷ eF 21 20 (inl a5) refl
    ∷ eF 19 21 (inr a6) refl
  ∷ []

eFact : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
  → Σ[ a ∈ Arr (F c) (F d) ] (arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))
eFact c d f = allFrom eFacts (fst (pos (src (fst f Mo.ₑ))))
                             (snd (pos (src (fst f Mo.ₑ)))) (eMem {c} {d} f)
                      {c} {d} f (λ _ → pos (src (fst f Mo.ₑ)))

F₁ : (c d : Mo.Crit₀) → Mo⁻.Crit₁ c d → Arr (F c) (F d)
F₁ c d f = fst (eFact c d f)

F₁id : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
  → arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) (F₁ c d f))
F₁id c d f = snd (eFact c d f)

VFact : ℕ → ℕ → Type
VFact x y = (c : Mo.Crit₀) → pos (c Mo.ᵥ) ≡ (x , y) → G (F c) ≡ c

vF : (x y : ℕ) {h : Bool→Type (vertexB x y)} (w : Vtx)
   → pos (CritAt x y {h} Mo.ᵥ) ≡ (x , y)     -- the position is Critical: it is its own sink
   → F (CritAt x y {h}) ≡ w                  -- the table finds it …
   → G w ≡ CritAt x y {h}                    -- … and finds it again
   → VFact x y
vF x y {h} w e₀ e₁ e₂ c hp =
  cong (λ z → G (F z)) γ ∙ cong G e₁ ∙ e₂ ∙ sym γ
  where γ : c ≡ CritAt x y {h}
        γ = CritEq (hp ∙ sym e₀)

vFacts : AllPos {P = VFact} vList
vFacts =
      vF 28 14 v0 refl refl refl
    ∷ vF 27 15 v1 refl refl refl
    ∷ vF 25 16 v2 refl refl refl
    ∷ vF 22 20 v3 refl refl refl
    ∷ vF 21 21 v4 refl refl refl
    ∷ vF 19 22 v5 refl refl refl
  ∷ []

R : (c : Mo.Crit₀) → G (F c) ≡ c
R c = allFrom vFacts (fst (pos (c Mo.ᵥ))) (snd (pos (c Mo.ᵥ))) (vMem c) c
              (λ _ → pos (c Mo.ᵥ))

--------------------------------------------------------------------------------
-- The two graphs are the same, and hence so are their realisations
--
-- In `Examples.VoevodskyMorse` both round-trips came from `Arr` being a
-- proposition, since no two edges of a forest are parallel.  Here two of them
-- are — but the two parallel pairs are split between `Tree` and `Loop`, and
-- each of those *is* a proposition, which is all that is needed: `F₁` sends an
-- edge into one of the two summands, and inside a summand there is nothing to
-- choose.  (This also keeps the value of `F₁` — a search through the whole
-- picture, transported along the gradient flow — from ever being unfolded.)

CritIsSet : isHSet Mo.Crit₀
CritIsSet = Mo.Crit₀IsHSet

arrowFib : {c d : Mo.Crit₀} {f f' : Mo⁻.Crit₁ c d} → arrow c d f ≡ arrow c d f' → f ≡ f'
arrowFib {c} {d} {f} {f'} β =
  subst2 (λ a b → PathP (λ i → Mo⁻.Crit₁ (a i) (b i)) f f')
    (CritIsSet c c (λ i → fst (β i)) refl)
    (CritIsSet d d (λ i → fst (snd (β i))) refl)
    (λ i → snd (snd (β i)))

isPropTree : (i j : Vtx) → isHProp (Tree i j)
isPropTree v5 v4 a0 a0 = refl
isPropTree v3 v2 a1 a1 = refl
isPropTree v1 v0 a2 a2 = refl
isPropTree v2 v1 a3 a3 = refl
isPropTree v4 v3 a5 a5 = refl

isPropLoop : (i j : Vtx) → isHProp (Loop i j)
isPropLoop v3 v2 a4 a4 = refl
isPropLoop v5 v4 a6 a6 = refl

-- An arrow of the graph, sent to the Morse complex and looked up again, is
-- itself: it is a tree edge or a loop again — the table says which — and there
-- is only one of those between any two vertices.
S₁ : (i j : Vtx) (a : Arr i j)
   → PathP (λ k → Arr (S i k) (S j k)) (F₁ (G i) (G j) (G₁ i j a)) a
S₁ v5 v4 (inl a0) = cong inl (isPropTree v5 v4 _ a0)
S₁ v5 v4 (inr a6) = cong inr (isPropLoop v5 v4 _ a6)
S₁ v3 v2 (inl a1) = cong inl (isPropTree v3 v2 _ a1)
S₁ v3 v2 (inr a4) = cong inr (isPropLoop v3 v2 _ a4)
S₁ v1 v0 (inl a2) = cong inl (isPropTree v1 v0 _ a2)
S₁ v2 v1 (inl a3) = cong inl (isPropTree v2 v1 _ a3)
S₁ v4 v3 (inl a5) = cong inl (isPropTree v4 v3 _ a5)

-- and the same in the other direction, read off `F₁id` directly: it is a path
-- of arrows, so its three components are the two ends and the arrow between
R₁ : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
   → PathP (λ k → Mo⁻.Crit₁ (R c k) (R d k)) (G₁ (F c) (F d) (F₁ c d f)) f
R₁ c d f = subst2
  (λ α₀ α₁ → PathP (λ k → Mo⁻.Crit₁ (α₀ k) (α₁ k)) (G₁ (F c) (F d) (F₁ c d f)) f)
  (CritIsSet (G (F c)) c (λ k → fst (β (~ k))) (R c))
  (CritIsSet (G (F d)) d (λ k → fst (snd (β (~ k)))) (R d))
  (λ k → snd (snd (β (~ k))))
  where β = F₁id c d f

Crit₁ᴹ≡Arr : GR.∣ Mo.Crit₀ , Mo⁻.Crit₁ ∣ ≡ GR.∣ Vtx , Arr ∣
Crit₁ᴹ≡Arr = GR.isoReal F F₁ G G₁ S S₁ R R₁



-- The realisation of the picture is the realisation of its Morse complex, which
-- is the graph above, which is a bouquet with one circle per edge outside the
-- spanning tree — and those are the two holes of the mug.
∣mug∣≡BouquetBool : ∣ V , E , Sq ∣ ≡ Bouquet Bool
∣mug∣≡BouquetBool =
  Mo.MorseTheorem ∙ Crit₁ᴹ≡Arr ∙ ∣Arr∣≡Bouquet ∙ cong Bouquet Loops≡Bool

