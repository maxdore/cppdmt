{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- Reading the Morse complex of a picture off the picture.
--
-- `ImageMatching` says which cells are Critical; this module turns that into
-- the data `GraphForest` wants, by making the Morse complex of a *concrete*
-- picture computable:
--
--   · `edgeAt x y` is the Critical edge at a position, and `arrAt x y` the
--     corresponding edge of the Morse complex, running from the Critical
--     vertex the source flows to, to the one the target flows to.  Both are
--     built from nothing but the position — every proof they need is a
--     `Bool→Type` of something that computes, hence an implicit argument that
--     Agda solves by η once the position is a literal;
--
--   · `edgeIs` says these are all of them: any edge of the Morse complex is
--     `arrAt` of the position of its source.  This is what lets a statement
--     about all edges be checked one position at a time.
--
-- The lists to check over come from `allVertices`: a Critical cell of a
-- picture with `N` rows and `W` columns sits in the box `(suc W) × (suc N)`,
-- so a single boolean computation enumerates them.
module ImageMorse where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

open import Agda.Builtin.String

open import ComplexMatching using (module Complex)
open import ComplexMorse using (module Morse)
open import ImageComplex
open import ImageMatching

private
  variable
    ℓ : Level

--------------------------------------------------------------------------------
-- Lists of positions
--
-- The Critical cells of a concrete picture are enumerated by a list, and the
-- facts about them by a list of proofs, one per entry.  `allFrom` is what
-- feeds an entry to an arbitrary cell that the box check has located.

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ→≡ : (m n : ℕ) → Bool→Type (eqℕ m n) → m ≡ n
eqℕ→≡ zero    zero    _ = refl
eqℕ→≡ (suc m) (suc n) h = cong suc (eqℕ→≡ m n h)

module _ {P : ℕ → ℕ → Type ℓ} where

  data AllPos : List (ℕ × ℕ) → Type ℓ where
    []  : AllPos []
    _∷_ : {x y : ℕ} {ps : List (ℕ × ℕ)} → P x y → AllPos ps → AllPos ((x , y) ∷ ps)

  infixr 5 _∷_

memB : ℕ → ℕ → List (ℕ × ℕ) → Bool
memB x y []             = false
memB x y ((a , b) ∷ ps) = (eqℕ x a and eqℕ y b) or memB x y ps

allFrom : {P : ℕ → ℕ → Type ℓ} {ps : List (ℕ × ℕ)}
  → AllPos {P = P} ps → (x y : ℕ) → Bool→Type (memB x y ps) → P x y
allFrom {ps = []}          []       x y ()
allFrom {P = P} {ps = (a , b) ∷ ps} (e ∷ es) x y m
  with or-elim (eqℕ x a and eqℕ y b) (memB x y ps) m
... | inl eq = subst (λ z → P (fst z) (snd z))
                 (sym (ΣPathP ( eqℕ→≡ x a (and-l _ _ eq)
                              , eqℕ→≡ y b (and-r _ _ eq)))) e
... | inr m' = allFrom es x y m'


module Forest (picture : List String) where

  open Match picture public
  module Mo = Morse complex matching
  -- the Morse complex is the Morse graph of the collapsed complex G⁻, so its
  -- gradient paths are the ones of `Mo⁻`, not the ones of the complex
  module Mo⁻ = Mo.Mo⁻

  --------------------------------------------------------------------------
  -- Critical cells at a given position
  --
  -- Everything here is stated for an arbitrary position and proves itself
  -- once the position is a literal: the implicit arguments are `Bool→Type`s
  -- of booleans that then compute to `true`, i.e. to `Unit`, and Agda solves
  -- them by η.

  -- a Critical vertex is determined by its position
  CritEq : {c d : Mo.Crit₀} → pos (c Mo.ᵥ) ≡ pos (d Mo.ᵥ) → c ≡ d
  CritEq p = Σ≡Prop Mo.isCritIsHProp (V≡ p)

  -- the two endpoints of the edge at a position
  srcV : (x y : ℕ) {hu : Bool→Type (vertexB x y)} → V
  srcV x y {hu} = (x , y) , hu

  tgtV : (x y : ℕ) {hv : Bool→Type (vertexB (suc x) y)} → V
  tgtV x y {hv} = (suc x , y) , hv

  -- where they flow
  srcSink : (x y : ℕ) {hu : Bool→Type (vertexB x y)} → Mo.Crit₀
  srcSink x y {hu} = Mo.sink (srcV x y {hu})

  tgtSink : (x y : ℕ) {hv : Bool→Type (vertexB (suc x) y)} → Mo.Crit₀
  tgtSink x y {hv} = Mo.sink (tgtV x y {hv})

  module _ (x y : ℕ)
    {hu : Bool→Type (vertexB x y)}          -- (x , y) is a vertex …
    {hv : Bool→Type (vertexB (suc x) y)}    -- … and so is the one to its right
    {he : Bool→Type (hEdgesB x y)}           -- they are joined by an edge …
    {nb : Bool→Type (not (black x y))}      -- … which caps no square …
    {vd : Bool→Type (vEdgesB x y)}           -- … and whose source goes down
    {hd : Bool→Type (vertexB x (suc y))}    -- (to a vertex, necessarily)
    where

    -- the edge itself, as an edge of the collapsed complex: it caps no square
    -- because the pixel below it is white
    edgeAt : Mo.Edges⁻
    edgeAt = srcV x y {hu} , tgtV x y {hv} , edge (inl (refl , he)) , ¬up
      where
      ¬up : ¬ Mo.isUp (srcV x y {hu} , tgtV x y {hv} , edge (inl (refl , he)))
      ¬up up = not-elim (black x y) nb (upBlack up)

    -- … and it is Critical: it is matched with no vertex either, because its
    -- source takes the edge below it instead
    ¬dnAt : ¬ (μ (srcV x y {hu}) ≡ tgtV x y {hv})
    ¬dnAt m = right≢down (x , y)
      (sym (cong pos m) ∙ cong pos (μdown (srcV x y {hu}) ((x , suc y) , hd) refl vd))

    -- … and hence the edge it contributes to the Morse complex
    arrAt : Mo⁻.Crit₁ (srcSink x y {hu}) (tgtSink x y {hv})
    arrAt = edgeAt , ¬dnAt , (srcV x y {hu} Mo⁻.⇝sink) , (tgtV x y {hv} Mo⁻.⇝sink)

  --------------------------------------------------------------------------
  -- … and these are all of them
  --
  -- An edge of the Morse complex is the Critical edge at the position of its
  -- source, run from sink to sink — so a property of all of them follows from
  -- one instance per position.

  -- the three cells and the two flows, bundled, so that a single `subst`
  -- moves a statement about `arrAt` to one about an arbitrary edge
  Arrow : Type₀
  Arrow = Σ[ c ∈ Mo.Crit₀ ] Σ[ d ∈ Mo.Crit₀ ] Mo⁻.Crit₁ c d

  arrow : (c d : Mo.Crit₀) → Mo⁻.Crit₁ c d → Arrow
  arrow c d f = c , d , f

  edgeIs : (x y : ℕ)
    {hu : Bool→Type (vertexB x y)} {hv : Bool→Type (vertexB (suc x) y)}
    {he : Bool→Type (hEdgesB x y)} {nb : Bool→Type (not (black x y))}
    {vd : Bool→Type (vEdgesB x y)} {hd : Bool→Type (vertexB x (suc y))}
    → {c d : Mo.Crit₀} (f : Mo⁻.Crit₁ c d)
    → pos (src (fst f Mo.ₑ)) ≡ (x , y)
    → arrow c d f ≡ arrow (srcSink x y {hu}) (tgtSink x y {hv})
                          (arrAt x y {hu} {hv} {he} {nb} {vd} {hd})
  edgeIs x y {hu} {hv} {he} {nb} {vd} {hd} {c} {d} f@((u , v , g , ¬up) , ¬dn , p , q) hp =
    ΣPathP (αc , ΣPathP (αd , ΣPathP (eq , ΣPathP (isProp→PathP (λ _ → isProp¬ _) _ _ ,
      isProp→PathP (λ i → isProp× (Mo⁻.⇝IsHProp (αc i)) (Mo⁻.⇝IsHProp (αd i))) _ _))))
    where
    -- the endpoints are the ones the position dictates
    pu : u ≡ srcV x y {hu}
    pu = V≡ hp

    pv : v ≡ tgtV x y {hv}
    pv = V≡ (fst (CritEdges (u , v , g) ¬dn ¬up) ∙ cong right hp)

    -- so the edge is the same one
    eq : (fst f) ≡ edgeAt x y {hu} {hv} {he} {nb} {vd} {hd}
    eq = Mo.ₑ-inj
           (ΣPathP (pu , ΣPathP (pv , isProp→PathP (λ i → E-isHProp _ _) _ _)))

    -- and the sinks are where its endpoints flow
    αc : c ≡ srcSink x y {hu}
    αc = Mo⁻.sinkUniqᶜ c (srcSink x y {hu})
           (subst (λ z → z Mo⁻.⇝ c Mo.ᵥ) pu p) (srcV x y {hu} Mo⁻.⇝sink)

    αd : d ≡ tgtSink x y {hv}
    αd = Mo⁻.sinkUniqᶜ d (tgtSink x y {hv})
           (subst (λ z → z Mo⁻.⇝ d Mo.ᵥ) pv q) (tgtV x y {hv} Mo⁻.⇝sink)
