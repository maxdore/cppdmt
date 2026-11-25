{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- The matching of `ImageMatching` on small pictures.
--
-- The first two sections are computations: the matching, its gradient flow and
-- the decision whether an edge caps a square all hold by `refl`.
--
-- The last two put the Morse theorem of `ComplexMorse` to work.  Both pictures
-- have a complex far too big to argue about by hand — the 2×2 block has 9
-- vertices, 12 edges and 4 squares, the ring 16 vertices, 24 edges and 8
-- squares — but their Morse complexes have one and two cells, and the theorem
-- says that is the same space.  Identifying the Morse complex takes just two
-- facts about the picture, each a single `refl` over the whole bitmap:
-- which vertices are Critical, and which edges are.
module Examples.ImageMatching where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.HITs.S1
open import Cubical.Relation.Nullary

open import Agda.Builtin.String

open import Prelude
open import ComplexMatching
open import CType2
open import ComplexMorse using (module Morse)
import CType1 as GR
open import GraphForest
open import ImageMatching
open import ImageMorse

--------------------------------------------------------------------------------
-- A single black pixel
--
--     v00 --- v10
--      |       |
--     v01 --- v11
--
-- Its three other corners flow into v11, and the top edge goes with the
-- square: one Critical cell, the vertex v11, as it must be for a disk.

module Dot where

  dot : List String
  dot = "#" ∷ []

  open Match dot

  v00 v10 v01 v11 : V
  v00 = (0 , 0) , tt
  v10 = (1 , 0) , tt
  v01 = (0 , 1) , tt
  v11 = (1 , 1) , tt

  -- v00 and v10 take the edge below them, v01 the one to its right …
  _ : pos (μ v00) ≡ (0 , 1)
  _ = refl

  _ : pos (μ v10) ≡ (1 , 1)
  _ = refl

  _ : pos (μ v01) ≡ (1 , 1)
  _ = refl

  -- … and v11, whose only black neighbour is to its north-west, is Critical
  _ : pos (μ v11) ≡ (1 , 1)
  _ = refl

  -- the gradient flow of the top left corner ends at v11
  _ : pos (fst (fst (flow v00))) ≡ (1 , 1)
  _ = refl

  -- the square is matched with its top edge, so that edge — and no other —
  -- caps a square
  _ : ν (cell 0 0 tt) ≡ tp
  _ = refl

  _ : Dec→Bool (isUp? (∂ (cell 0 0 tt) tp)) ≡ true
  _ = refl

  _ : Dec→Bool (isUp? (∂ (cell 0 0 tt) bt)) ≡ false
  _ = refl

  _ : Dec→Bool (isUp? (∂ (cell 0 0 tt) lf)) ≡ false
  _ = refl

--------------------------------------------------------------------------------
-- Two pixels meeting at a corner
--
--        .#
--        #.
--
-- Gradient paths only run right and down, so the two south-east tips (2 , 1)
-- and (1 , 2) are both Critical.  The complex is a wedge of two disks, so a
-- Critical edge has to make up for the extra vertex — and there is one: the
-- horizontal edge from (1 , 1) to (2 , 1), which has a black pixel above it,
-- a white one below it and a black one to its south-west.

module Wedge where

  wedge : List String
  wedge = ".#" ∷ "#." ∷ []

  open Forest wedge

  -- the corner the two pixels share flows into the lower one
  _ : pos (μ ((1 , 1) , tt)) ≡ (1 , 2)
  _ = refl

  _ : pos (μ ((1 , 0) , tt)) ≡ (1 , 1)
  _ = refl

  -- the two south-east tips are Critical
  _ : pos (μ ((2 , 1) , tt)) ≡ (2 , 1)
  _ = refl

  _ : pos (μ ((1 , 2) , tt)) ≡ (1 , 2)
  _ = refl

  -- the edge (1 , 1) — (2 , 1): its source is matched downwards instead, and
  -- it caps no square, so it is Critical
  e : Edges
  e = ((1 , 1) , tt) , ((2 , 1) , tt) , edge (inl (refl , tt))

  _ : Dec→Bool (V-discrete (μ (src e)) (tgt e)) ≡ false
  _ = refl

  _ : Dec→Bool (isUp? e) ≡ false
  _ = refl



  ------------------------------------------------------------------------
  -- … and the Morse complex is a segment, so the wedge is contractible
  --
  -- Two Critical vertices joined by one Critical edge: a tree, which
  -- `GraphForest` collapses onto its root.  This is the same argument the
  -- 64×64 picture of `Examples.VoevodskyMorse` needs, at a size where it fits
  -- on a page.

  data Vtx : Type where
    vA vB : Vtx                 -- vA is (2 , 1), vB is (1 , 2)

  data Arr : Vtx → Vtx → Type where
    aB : Arr vB vA              -- the Critical edge at (1 , 1)

  ι : Unit → Vtx
  ι _ = vA

  root : Vtx → Unit
  root _ = tt

  rootIsRoot : (r : Unit) → root (ι r) ≡ r
  rootIsRoot tt = refl

  rootPath : (v : Vtx) → Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι (root v) ∣₀) (GR.∣ v ∣₀)
  rootPath vA = refl
  rootPath vB = sym (GR.∣ vB ⇒ vA ∋ aB ∣₁)

  contrEdge : {i j : Vtx} (a : Arr i j)
    → Σ[ α ∈ root i ≡ root j ]
        PathP (λ k → Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι (α k) ∣₀) (GR.∣ i ⇒ j ∋ a ∣₁ k))
              (rootPath i) (rootPath j)
  contrEdge aB = refl , λ i j → GR.∣ vB ⇒ vA ∋ aB ∣₁ (i ∨ ~ j)

  isPropArr : (i j : Vtx) → isProp (Arr i j)
  isPropArr vB vA aB aB = refl

  ∣Arr∣≡Unit : GR.∣ Vtx , Arr ∣ ≡ Unit
  ∣Arr∣≡Unit = ForestCollapse Unit ι root rootIsRoot rootPath contrEdge

  -- the dictionary between that graph and the Morse complex
  G : Vtx → Mo.Crit₀
  G vA = tgtSink 1 1
  G vB = srcSink 1 1

  F : Mo.Crit₀ → Vtx
  F c = if (eqℕ (fst (pos (c Mo.ᵥ))) 2 and eqℕ (snd (pos (c Mo.ᵥ))) 1) then vA else vB

  S : (v : Vtx) → F (G v) ≡ v
  S vA = refl
  S vB = refl

  G₁ : (i j : Vtx) → Arr i j → Mo⁻.Crit₁ (G i) (G j)
  G₁ vB vA aB = arrAt 1 1

  -- the two enumerations: the picture has one Critical edge and two Critical
  -- vertices, and `allVertices` checks that nothing else is Critical
  CritEdgesB CritVB : ℕ → ℕ → Bool
  CritEdgesB x y = hEdgesB x y and (not (black x y) and vEdgesB x y)
  CritVB   x y = not (vEdgesB x y) and not (hEdgesB x y and not (black x y))

  eList vList : List (ℕ × ℕ)
  eList = (1 , 1) ∷ []
  vList = (2 , 1) ∷ (1 , 2) ∷ []

  eBox : (u : V) → Bool→Type (not (CritEdgesB (fst (pos u)) (snd (pos u)))
                              or memB (fst (pos u)) (snd (pos u)) eList)
  eBox = allVertices (λ x y → not (CritEdgesB x y) or memB x y eList) tt

  vBox : (u : V) → Bool→Type (not (CritVB (fst (pos u)) (snd (pos u)))
                              or memB (fst (pos u)) (snd (pos u)) vList)
  vBox = allVertices (λ x y → not (CritVB x y) or memB x y vList) tt

  eMem : {c d : Mo.Crit₀} (f : Mo⁻.Crit₁ c d)
    → Bool→Type (memB (fst (pos (src (fst f Mo.ₑ)))) (snd (pos (src (fst f Mo.ₑ)))) eList)
  eMem (((((x , y) , hu) , v , g , ¬up) , ¬dn , _ , _))
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

  -- so every cell of the Morse complex is one of those, …
  EFact : ℕ → ℕ → Type
  EFact x y = {c d : Mo.Crit₀} (f : Mo⁻.Crit₁ c d) → pos (src (fst f Mo.ₑ)) ≡ (x , y)
            → Σ[ a ∈ Arr (F c) (F d) ]
                (arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))

  eFacts : AllPos {P = EFact} eList
  eFacts = eF ∷ []
    where
    eF : EFact 1 1
    eF {c} {d} f h =
      subst2 (λ i j → Σ[ a ∈ Arr i j ] (arrow c d f ≡ arrow (G i) (G j) (G₁ i j a)))
        (sym (cong F (cong fst β))) (sym (cong F (cong (λ z → fst (snd z)) β)))
        (aB , β)
      where β = edgeIs 1 1 f h

  eFact : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
    → Σ[ a ∈ Arr (F c) (F d) ]
        (arrow c d f ≡ arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))
  eFact c d f = allFrom eFacts (fst (pos (src (fst f Mo.ₑ))))
                               (snd (pos (src (fst f Mo.ₑ)))) (eMem {c} {d} f)
                        {c} {d} f (λ _ → pos (src (fst f Mo.ₑ)))

  F₁ : (c d : Mo.Crit₀) → Mo⁻.Crit₁ c d → Arr (F c) (F d)
  F₁ c d f = fst (eFact c d f)

  VFact : ℕ → ℕ → Type
  VFact x y = (c : Mo.Crit₀) → pos (c Mo.ᵥ) ≡ (x , y) → G (F c) ≡ c

  vFacts : AllPos {P = VFact} vList
  vFacts = (λ c h → cong (λ z → G (F z)) (CritEq {c} {G vA} h) ∙ sym (CritEq {c} {G vA} h))
         ∷ (λ c h → cong (λ z → G (F z)) (CritEq {c} {G vB} h) ∙ sym (CritEq {c} {G vB} h))
         ∷ []

  R : (c : Mo.Crit₀) → G (F c) ≡ c
  R c = allFrom vFacts (fst (pos (c Mo.ᵥ))) (snd (pos (c Mo.ᵥ))) (vMem c) c
                (λ _ → pos (c Mo.ᵥ))

  -- … the two graphs are the same, …
  arrowFib : {c d : Mo.Crit₀} {f f' : Mo⁻.Crit₁ c d} → arrow c d f ≡ arrow c d f' → f ≡ f'
  arrowFib {c} {d} {f} {f'} β =
    subst2 (λ a b → PathP (λ i → Mo⁻.Crit₁ (a i) (b i)) f f')
      (Mo.Crit₀IsHSet c c (λ i → fst (β i)) refl)
      (Mo.Crit₀IsHSet d d (λ i → fst (snd (β i))) refl)
      (λ i → snd (snd (β i)))

  isPropCrit₁ᴹ : {c d : Mo.Crit₀} → isProp (Mo⁻.Crit₁ c d)
  isPropCrit₁ᴹ {c} {d} f f' = arrowFib
    (snd (eFact c d f)
      ∙ cong (λ a → arrow (G (F c)) (G (F d)) (G₁ (F c) (F d) a))
          (isPropArr (F c) (F d) (F₁ c d f) (F₁ c d f'))
      ∙ sym (snd (eFact c d f')))

  S₁ : (i j : Vtx) (a : Arr i j)
     → PathP (λ k → Arr (S i k) (S j k)) (F₁ (G i) (G j) (G₁ i j a)) a
  S₁ i j a = toPathP (isPropArr i j (transport (λ k → Arr (S i k) (S j k))
                                       (F₁ (G i) (G j) (G₁ i j a))) a)

  R₁ : (c d : Mo.Crit₀) (f : Mo⁻.Crit₁ c d)
     → PathP (λ k → Mo⁻.Crit₁ (R c k) (R d k)) (G₁ (F c) (F d) (F₁ c d f)) f
  R₁ c d f = toPathP (isPropCrit₁ᴹ {c} {d}
    (transport (λ k → Mo⁻.Crit₁ (R c k) (R d k)) (G₁ (F c) (F d) (F₁ c d f))) f)

  -- … and so the wedge of two disks is a point
  ∣wedge∣≡Unit : ∣ V , E , Sq ∣ ≡ Unit
  ∣wedge∣≡Unit = Mo.MorseTheorem
               ∙ GR.isoReal F F₁ G G₁ S S₁ R R₁ ∙ ∣Arr∣≡Unit

  isContr∣wedge∣ : isContr (∣ V , E , Sq ∣)
  isContr∣wedge∣ = subst isContr (sym ∣wedge∣≡Unit) isContrUnit

--------------------------------------------------------------------------------
-- A 2×2 block of pixels is contractible
--
-- Its Morse complex has a single vertex — the bottom right corner of the block
-- — and no edges at all, so it is the point; by the Morse theorem so is the
-- realisation of the complex itself.

module Square where

  square : List String
  square =
      "...."
    ∷ ".##."
    ∷ ".##."
    ∷ "...."
    ∷ []

  open Match square
  module Mo = Morse complex matching
  -- the Morse complex's gradient paths are the ones of the collapsed complex
  module Mo⁻ = Mo.Mo⁻

  ------------------------------------------------------------------------
  -- The Critical vertices: only the bottom right corner of the block

  tip : Mo.Crit₀
  tip = ((3 , 3) , tt) , refl

  -- Every vertex has an edge below it, or an edge to its right that the square
  -- below does not claim, or is the tip.  This is a property of all 25 lattice
  -- points the picture can reach, and `allVertices` checks it by computation.
  matchedB : ℕ → ℕ → Bool
  matchedB x y = vEdgesB x y
              or ((hEdgesB x y and not (black x y))
              or (Dec→Bool (discreteℕ x 3) and Dec→Bool (discreteℕ y 3)))

  tipPos : (u : V) → μ u ≡ u → pos u ≡ (3 , 3)
  tipPos u p = go (allVertices matchedB tt u)
    where
    x = fst (pos u)
    y = snd (pos u)

    go : Bool→Type (matchedB x y) → pos u ≡ (3 , 3)
    go m with or-elim (vEdgesB x y) _ m
    ... | inl d  = absurd (fst (CritVertex u p) d)
    ... | inr m' with or-elim (hEdgesB x y and not (black x y)) _ m'
    ...          | inl rb = absurd (not-elim (black x y) (and-r _ _ rb)
                                     (snd (CritVertex u p) (and-l _ _ rb)))
    ...          | inr eq = ΣPathP (DecBool→Dec (discreteℕ x 3) (and-l _ _ eq)
                                  , DecBool→Dec (discreteℕ y 3) (and-r _ _ eq))

  uniqTip : (c : Mo.Crit₀) → tip ≡ c
  uniqTip (u , p) = Σ≡Prop Mo.isCritIsHProp (V≡ (sym (tipPos u p)))

  ------------------------------------------------------------------------
  -- The Critical edges: there are none
  --
  -- A Critical edge is horizontal with a white pixel below it and a black one
  -- to its south-west, and no lattice point of this picture looks like that.

  noEdgesB : ℕ → ℕ → Bool
  noEdgesB x y = not (hEdgesB x y and (not (black x y) and vEdgesB x y))

  noEdges : (c d : Mo.Crit₀) → Mo⁻.Crit₁ c d → ⊥
  noEdges c d ((u , v , f , ¬up) , ¬dn , _ , _) =
    not-elim _ (allVertices noEdgesB tt u)
      (and-i _ _ r (and-i _ _ (not-i _ ¬b) vd))
    where
    cr = CritEdges (u , v , f) ¬dn ¬up
    r  = fst (snd cr)
    ¬b = fst (snd (snd cr))
    vd = snd (snd (snd cr))

  ------------------------------------------------------------------------
  -- … so the Morse complex is the graph with one vertex and no edges

  -- `isoReal` takes an isomorphism of graphs — on vertices and on edges, in
  -- both directions, with the two round-trips — to one of their realisations.
  -- Here it is the graph with one vertex and no edges, both ways round.
  -- Morse≡Unit : Mo.∣Morse∣ ≡ Unit
  -- Morse≡Unit = noSq ∙ GR.isoReal
  --     (λ _ → tt)   noEdges
  --     (λ _ → tip)  (λ x y e → absurd e)
  --     (λ _ → refl) (λ x y e → absurd e)
  --     uniqTip      (λ c d e → absurd (noEdges c d e))
  --   ∙ sym GR.⊤≡∣⊥₁∣

  ∣square∣≡Unit : ∣ V , E , Sq ∣ ≡ Unit
  ∣square∣≡Unit = Mo.MorseTheorem ∙ GR.isoReal
                                (λ _ → tt)   noEdges
                                (λ _ → tip)  (λ x y e → absurd e)
                                (λ _ → refl) (λ x y e → absurd e)
                                uniqTip      (λ c d e → absurd (noEdges c d e))
                                ∙ sym GR.⊤≡∣⊥₁∣

  isContr∣square∣ : isContr ∣ V , E , Sq ∣
  isContr∣square∣ = subst isContr (sym ∣square∣≡Unit) isContrUnit

--------------------------------------------------------------------------------
-- A ring of pixels is a circle
--
-- The Morse complex now keeps one edge as well: the top edge of the hole,
-- which is horizontal, has a white pixel below it and a black one to its
-- south-west.  A vertex and a loop is the circle.

module Circle where

  circle : List String
  circle =
      "....."
    ∷ ".###."
    ∷ ".#.#."
    ∷ ".###."
    ∷ "....."
    ∷ []

  open Match circle
  module Mo = Morse complex matching
  -- the Morse complex's gradient paths are the ones of the collapsed complex
  module Mo⁻ = Mo.Mo⁻

  ------------------------------------------------------------------------
  -- The Critical vertices: again only the bottom right corner

  tip : Mo.Crit₀
  tip = ((4 , 4) , tt) , refl

  -- as before: every vertex is matched, or is the tip (36 lattice points)
  matchedB : ℕ → ℕ → Bool
  matchedB x y = vEdgesB x y
              or ((hEdgesB x y and not (black x y))
              or (Dec→Bool (discreteℕ x 4) and Dec→Bool (discreteℕ y 4)))

  tipPos : (u : V) → μ u ≡ u → pos u ≡ (4 , 4)
  tipPos u p = go (allVertices matchedB tt u)
    where
    x = fst (pos u)
    y = snd (pos u)

    go : Bool→Type (matchedB x y) → pos u ≡ (4 , 4)
    go m with or-elim (vEdgesB x y) _ m
    ... | inl d  = absurd (fst (CritVertex u p) d)
    ... | inr m' with or-elim (hEdgesB x y and not (black x y)) _ m'
    ...          | inl rb = absurd (not-elim (black x y) (and-r _ _ rb)
                                     (snd (CritVertex u p) (and-l _ _ rb)))
    ...          | inr eq = ΣPathP (DecBool→Dec (discreteℕ x 4) (and-l _ _ eq)
                                  , DecBool→Dec (discreteℕ y 4) (and-r _ _ eq))

  uniqTip : (c : Mo.Crit₀) → tip ≡ c
  uniqTip (u , p) = Σ≡Prop Mo.isCritIsHProp (V≡ (sym (tipPos u p)))

  -- every vertex flows into the tip
  toTip : (u : V) → u Mo⁻.⇝ tip Mo.ᵥ
  toTip u = subst (λ c → u Mo⁻.⇝ c Mo.ᵥ) (sym (uniqTip (Mo.sink u))) (u Mo⁻.⇝sink)

  ------------------------------------------------------------------------
  -- The Critical edges: only the top edge of the hole

  -- The horizontal edge (2 , 2) — (3 , 2), which runs along the top of the
  -- hole.  It is matched with neither: its source takes the edge below it
  -- instead — μ (2 , 2) is (2 , 3), and 2 ≢ 3 — and the pixel below it, the
  -- hole itself, is white, so `upBlack` already lands in the empty type.
  loop₁ : Mo.Edges⁻
  loop₁ = ((2 , 2) , tt) , ((3 , 2) , tt) , edge (inl (refl , tt)) , upBlack

  -- the same enumeration as before, now with the one Critical edge allowed
  oneEdgesB : ℕ → ℕ → Bool
  oneEdgesB x y = not (hEdgesB x y and (not (black x y) and vEdgesB x y))
              or (Dec→Bool (discreteℕ x 2) and Dec→Bool (discreteℕ y 2))

  -- and it is the only one: a Critical edge starts at (2 , 2), and a
  -- horizontal edge is determined by where it starts
  edgeUniq : (e : Mo.Edges⁻) → ¬ (μ (fst e) ≡ fst (snd e)) → e Mo.ₑ ≡ loop₁ Mo.ₑ
  edgeUniq (u , v , f , ¬up) ¬dn =
    ΣPathP (V≡ srcPos , ΣPathP (V≡ tgtPos ,
      isProp→PathP (λ i → E-isHProp _ _) _ _))
    where
    x = fst (pos u)
    y = snd (pos u)

    cr  = CritEdges (u , v , f) ¬dn ¬up
    h   = fst cr
    r   = fst (snd cr)
    ¬b  = fst (snd (snd cr))
    vd  = snd (snd (snd cr))

    go : Bool→Type (oneEdgesB x y) → pos u ≡ (2 , 2)
    go m with or-elim (not (hEdgesB x y and (not (black x y) and vEdgesB x y))) _ m
    ... | inl ¬ce = absurd (not-elim _ ¬ce (and-i _ _ r (and-i _ _ (not-i _ ¬b) vd)))
    ... | inr eq = ΣPathP (DecBool→Dec (discreteℕ x 2) (and-l _ _ eq)
                          , DecBool→Dec (discreteℕ y 2) (and-r _ _ eq))

    srcPos : pos u ≡ (2 , 2)
    srcPos = go (allVertices oneEdgesB tt u)

    tgtPos : pos v ≡ (3 , 2)
    tgtPos = h ∙ cong right srcPos

  -- so the Morse complex has exactly one edge, from the tip to itself
  loopᴹ : Mo⁻.Crit₁ tip tip
  loopᴹ = loop₁
        , (λ dn → znots (injSuc (injSuc (cong (λ z → fst (pos z)) dn))))
        , toTip _ , toTip _

  isPropCrit₁ᴹ : (c d : Mo.Crit₀) → isProp (Mo⁻.Crit₁ c d)
  isPropCrit₁ᴹ c d (e , ¬dn , p , q) (e' , ¬dn' , p' , q') =
    ΣPathP (eq , ΣPathP (isProp→PathP (λ _ → isProp¬ _) _ _
      , isProp→PathP (λ i → isProp× (Mo⁻.⇝IsHProp c) (Mo⁻.⇝IsHProp d)) _ _))
    where
    eq : e ≡ e'
    eq = Mo.ₑ-inj (edgeUniq e ¬dn ∙ sym (edgeUniq e' ¬dn'))

  ------------------------------------------------------------------------
  -- … and a vertex with a loop is the circle

  -- one vertex and one edge, matched up with the graph `⊤₁` whose realisation
  -- `GraphRealisation` identifies with the circle
  Morse≡S¹ : GR.∣ Mo.Crit₀ , Mo⁻.Crit₁ ∣ ≡ S¹
  Morse≡S¹ = GR.isoReal
      (λ _ → tt)   (λ c d e → tt)
      (λ _ → tip)  (λ x y e → loopᴹ)
      (λ _ → refl) (λ x y e → isPropUnit _ _)
      uniqTip      (λ c d e → isProp→PathP
                      (λ i → isPropCrit₁ᴹ (uniqTip c i) (uniqTip d i)) _ _)
    ∙ sym GR.S¹≡∣⊤₁∣

  ∣circle∣≡S¹ : ∣ V , E , Sq ∣ ≡ S¹
  ∣circle∣≡S¹ = Mo.MorseTheorem ∙ Morse≡S¹

  ∣circle∣≃S¹ : ∣ V , E , Sq ∣ ≃ S¹
  ∣circle∣≃S¹ = pathToEquiv ∣circle∣≡S¹

