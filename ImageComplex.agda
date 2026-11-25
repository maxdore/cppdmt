{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- Every black pixel gives a 2-cell; the 1- and 0-cells are the ones induced by
-- those squares: a lattice point is a vertex exactly when one of the (at most
-- four) pixels around it is black, and a lattice segment is an edge exactly
-- when one of the (at most two) pixels it separates is black.  Cells are
-- *computed* from coordinates rather than freely generated, so neighbouring
-- black pixels share their faces on the nose — see the `refl`s at the end.
module ImageComplex where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

open import Agda.Builtin.Char
open import Agda.Builtin.String

open import Prelude
open import GraphMatching using (Graph)
open import ComplexMatching using (Complex ; module Cells )
open import CType2

-- One character per pixel, `#` for black; row y is the y-th string, and column
-- x the x-th character of it.

module Image (picture : List String) where

  -- the n-th element of a list, with a default outside the range
  at : {A : Type₀} → A → List A → ℕ → A
  at d []       _       = d
  at d (a ∷ _)  zero    = a
  at d (_ ∷ as) (suc n) = at d as n

  -- is the pixel in column x of row y black?  Everything outside the bitmap is
  -- white, so the complex below is finite.
  black : ℕ → ℕ → Bool
  black x y = primCharEquality '#' (at '.' (primStringToList (at "" picture y)) x)

  -- Pixel (x , y) is the unit square
  --
  --       (x , y) ---------- (suc x , y)
  --          |                    |
  --          |      (x , y)       |          (y grows downwards, as in
  --          |                    |           the bitmap)
  --     (x , suc y) ------ (suc x , suc y)
  --
  -- so the pixels meeting the lattice point (x , y) are (x , y) itself to its
  -- south-east, (x-1 , y) to its south-west, (x , y-1) to its north-east and
  -- (x-1 , y-1) to its north-west — the cases below are exactly the ones where
  -- those neighbours exist.

  Pos : Type₀
  Pos = ℕ × ℕ

  right down : Pos → Pos
  right (x , y) = suc x , y
  down  (x , y) = x , suc y

  pix : Pos → Bool
  pix (x , y) = black x y

  -- the neighbours of the lattice point (x , y) other than the pixel (x , y)
  -- itself, `false` where they fall outside the first quadrant
  pxSW pxNE pxNW : ℕ → ℕ → Bool
  pxSW zero    _       = false
  pxSW (suc x) y       = black x y
  pxNE _       zero    = false
  pxNE x       (suc y) = black x y
  pxNW zero    _       = false
  pxNW _       zero    = false
  pxNW (suc x) (suc y) = black x y

  -- (x , y) is a 0-cell iff one of the pixels around it is black
  vertexB vRest vRest' : ℕ → ℕ → Bool
  vertexB x y = black x y or vRest x y
  vRest   x y = pxSW x y or vRest' x y
  vRest'  x y = pxNE x y or pxNW x y

  -- the horizontal segment (x , y) — (suc x , y) is a 1-cell iff one of the two
  -- pixels it separates — (x , y) below it, (x , y-1) above it — is black
  pxAbove hEdgesB : ℕ → ℕ → Bool
  pxAbove x zero    = false
  pxAbove x (suc y) = black x y
  hEdgesB  x y       = black x y or pxAbove x y

  -- likewise for the vertical segment (x , y) — (x , suc y), separating the
  -- pixels (x , y) on its right and (x-1 , y) on its left
  pxLeft vEdgesB : ℕ → ℕ → Bool
  pxLeft zero    y = false
  pxLeft (suc x) y = black x y
  vEdgesB x       y = black x y or pxLeft x y

  vertexP hEdgesP vEdgesP : Pos → Bool
  vertexP (x , y) = vertexB x y
  hEdgesP  (x , y) = hEdgesB x y
  vEdgesP  (x , y) = vEdgesB x y

  -- 0-cells: the lattice points touching a black pixel
  V : Type₀
  V = Σ[ p ∈ Pos ] Bool→Type (vertexP p)

  pos : V → Pos
  pos = fst

  -- 1-cells: a segment to the right or downwards, bounding a black pixel.  This
  -- is wrapped in a record rather than left as a plain ⊎ so that `E` is
  -- injective, which is what lets Agda read the corners of a square off the
  -- types of its four boundary edges.
  record E (u v : V) : Type₀ where
    constructor edge
    field
      step : ((pos v ≡ right (pos u)) × Bool→Type (hEdgesP (pos u)))
          ⊎ ((pos v ≡ down  (pos u)) × Bool→Type (vEdgesP (pos u)))

  -- 2-cells: the black pixels.  The three equations pin the corners b c d down
  -- to the ones of the pixel at a, which rules out the degenerate squares that
  -- the four boundary edges alone would still permit (e.g. top = left).
  Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type₀
  Sq {a} {b} {c} {d} _ _ _ _ =
      (pos b ≡ right (pos a))
    × (pos c ≡ down (pos a))
    × (pos d ≡ right (down (pos a)))
    × Bool→Type (pix (pos a))

  open Cells V E Sq

  --------------------------------------------------------------------------------
  -- … form a complex

  private
    n≢sn : (n : ℕ) → ¬ n ≡ suc n
    n≢sn zero    p = znots p
    n≢sn (suc n) p = n≢sn n (injSuc p)

    ≢right : (p : Pos) → ¬ p ≡ right p
    ≢right p q = n≢sn (fst p) (cong fst q)

    ≢down : (p : Pos) → ¬ p ≡ down p
    ≢down p q = n≢sn (snd p) (cong snd q)

    right≢down : (p : Pos) → ¬ right p ≡ down p
    right≢down p q = n≢sn (fst p) (sym (cong fst q))

    Pos-discrete : Discrete Pos
    Pos-discrete = discreteΣ discreteℕ (λ _ → discreteℕ)

    Pos-isHSet : isHSet Pos
    Pos-isHSet = isSet× isSetℕ isSetℕ

    -- the endpoints of two equal edges agree
    srcP : {e f : Edges} → e ≡ f → pos (src e) ≡ pos (src f)
    srcP p = cong (λ z → pos (src z)) p

    tgtP : {e f : Edges} → e ≡ f → pos (tgt e) ≡ pos (tgt f)
    tgtP p = cong (λ z → pos (tgt z)) p

  V-discrete : Discrete V
  V-discrete u v with Pos-discrete (pos u) (pos v)
  ... | yes p = yes (Σ≡Prop (λ _ → isPropBool→Type) p)
  ... | no ¬p = no λ q → ¬p (cong pos q)

  E-isIrrefl : (u : V) → ¬ E u u
  E-isIrrefl u (edge (inl (p , _))) = ≢right (pos u) p
  E-isIrrefl u (edge (inr (p , _))) = ≢down  (pos u) p

  E-isHProp : (u v : V) → isHProp (E u v)
  E-isHProp u v (edge s) (edge s') i = edge
    (isProp⊎ (isProp× (Pos-isHSet _ _) isPropBool→Type)
            (isProp× (Pos-isHSet _ _) isPropBool→Type)
            (λ (p , _) (q , _) → right≢down (pos u) (sym p ∙ q))
            s s' i)

  Sq-isHProp : {a b c d : V} (t : E a b) (bo : E c d) (l : E a c) (r : E b d)
    → isHProp (Sq t bo l r)
  Sq-isHProp _ _ _ _ =
    isProp× (Pos-isHSet _ _) (isProp× (Pos-isHSet _ _)
      (isProp× (Pos-isHSet _ _) isPropBool→Type))

  -- The four sides of a pixel are pairwise distinct because its four corners
  -- are: each case below compares the sources (or the targets) of two faces and
  -- reads off  x ≡ suc x  or  y ≡ suc y.
  ∂-inj : (s : Squares) {i j : Side} → ∂ s i ≡ ∂ s j → i ≡ j
  ∂-inj s {tp} {tp} e = refl
  ∂-inj s {bt} {bt} e = refl
  ∂-inj s {lf} {lf} e = refl
  ∂-inj s {rt} {rt} e = refl
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {tp} {bt} e =
    absurd (≢down (pos a) (srcP e ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {tp} {lf} e =
    absurd (right≢down (pos a) (sym pb ∙ tgtP e ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {tp} {rt} e =
    absurd (≢right (pos a) (srcP e ∙ pb))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {bt} {tp} e =
    absurd (≢down (pos a) (sym (srcP e) ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {bt} {lf} e =
    absurd (≢down (pos a) (sym (srcP e) ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {bt} {rt} e =
    absurd (right≢down (pos a) (sym pb ∙ sym (srcP e) ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {lf} {tp} e =
    absurd (right≢down (pos a) (sym pb ∙ sym (tgtP e) ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {lf} {bt} e =
    absurd (≢down (pos a) (srcP e ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {lf} {rt} e =
    absurd (≢right (pos a) (srcP e ∙ pb))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {rt} {tp} e =
    absurd (≢right (pos a) (sym (srcP e) ∙ pb))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {rt} {bt} e =
    absurd (right≢down (pos a) (sym pb ∙ srcP e ∙ pc))
  ∂-inj (a , _ , _ , _ , _ , _ , _ , _ , pb , pc , _ , _) {rt} {lf} e =
    absurd (≢right (pos a) (sym (srcP e) ∙ pb))


  -- Every black pixel is a 2-cell
  --
  -- The witnesses below are the "one of the neighbours is black" disjuncts of
  -- `vertexB`, `hEdgesB` and `vEdgesB`, instantiated at the pixel itself.

  private
    -- `_or_` is not injective, so the two disjuncts have to be given explicitly
    or-l : (b c : Bool) → Bool→Type b → Bool→Type (b or c)
    or-l false c ()
    or-l true  c _ = tt

    or-r : (b c : Bool) → Bool→Type c → Bool→Type (b or c)
    or-r false c h = h
    or-r true  c _ = tt

    -- the four corners of pixel (x , y): it is the south-east neighbour of its
    -- own north-west corner, the south-west neighbour of its north-east corner,
    -- and so on
    vtx-nw : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (vertexB x y)
    vtx-nw x y h = or-l (black x y) (vRest x y) h

    vtx-ne : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (vertexB (suc x) y)
    vtx-ne x y h =
      or-r (black (suc x) y) (vRest (suc x) y)
        (or-l (black x y) (vRest' (suc x) y) h)

    vtx-sw : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (vertexB x (suc y))
    vtx-sw x y h =
      or-r (black x (suc y)) (vRest x (suc y))
        (or-r (pxSW x (suc y)) (vRest' x (suc y))
          (or-l (black x y) (pxNW x (suc y)) h))

    vtx-se : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (vertexB (suc x) (suc y))
    vtx-se x y h =
      or-r (black (suc x) (suc y)) (vRest (suc x) (suc y))
        (or-r (pxSW (suc x) (suc y)) (vRest' (suc x) (suc y))
          (or-r (pxNE (suc x) (suc y)) (black x y) h))

    -- and its four sides
    edge-tp : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (hEdgesB x y)
    edge-tp x y h = or-l (black x y) (pxAbove x y) h

    edge-bt : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (hEdgesB x (suc y))
    edge-bt x y h = or-r (black x (suc y)) (black x y) h

    edge-lf : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (vEdgesB x y)
    edge-lf x y h = or-l (black x y) (pxLeft x y) h

    edge-rt : (x y : ℕ) → Bool→Type (black x y) → Bool→Type (vEdgesB (suc x) y)
    edge-rt x y h = or-r (black (suc x) y) (black x y) h

  cell : (x y : ℕ) → Bool→Type (black x y) → Squares
  cell x y h = a , b , c , d , t , bo , l , r , refl , refl , refl , h
    where
    a b c d : V
    a = (x     , y)     , vtx-nw x y h
    b = (suc x , y)     , vtx-ne x y h
    c = (x     , suc y) , vtx-sw x y h
    d = (suc x , suc y) , vtx-se x y h

    t : E a b
    t = edge (inl (refl , edge-tp x y h))

    bo : E c d
    bo = edge (inl (refl , edge-bt x y h))

    l : E a c
    l = edge (inr (refl , edge-lf x y h))

    r : E b d
    r = edge (inr (refl , edge-rt x y h))


  complex : Complex V E Sq
  complex = record
    { graph = record
      { V-discrete = V-discrete
      ; E-isIrrefl = E-isIrrefl
      ; E-isHProp  = E-isHProp
      }
      ; Sq-isHProp = Sq-isHProp
      ; ∂-inj      = ∂-inj
    }

