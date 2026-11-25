{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- Two black pixels touching only at a corner
--
--        .#              (1 , 0) ---- (2 , 0)
--        #.                 |  (1 , 0)  |
--                (0 , 1) ---- (1 , 1) ---- (2 , 1)
--                   |  (0 , 1)  |
--                (0 , 2) ---- (1 , 2)
--
-- The lattice point (1 , 1) is the south-west corner of the pixel (1 , 0) and
-- the north-east corner of the pixel (0 , 1).  As the cells of `ImageComplex`
-- are computed from coordinates, it is one and the same 0-cell for both, so
-- the two squares are glued at it and the complex is connected: black pixels
-- are 8-connected.  The picture is the one of `Examples.ImageMatching.Wedge`,
-- where the Morse theorem shows that the realisation is even contractible.
module Examples.Corner where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Agda.Builtin.String

open import Prelude
open import ComplexMatching using (module Cells)
open import CType2
open import ImageComplex
import Examples.ImageMatching as EIM

corner : List String
corner = ".#" ∷ "#." ∷ []

open Image corner
open Cells V E Sq

-- the two black pixels, as 2-cells
pixNE pixSW : Squares
pixNE = cell 1 0 tt
pixSW = cell 0 1 tt

-- the lattice point between them is a 0-cell …
mid : V
mid = (1 , 1) , tt

-- … which is the end of the left side and the start of the bottom side of the
-- upper pixel, …
_ : tgt (∂ pixNE lf) ≡ mid
_ = refl

_ : src (∂ pixNE bt) ≡ mid
_ = refl

-- … and the end of the top side and the start of the right side of the lower
-- one
_ : tgt (∂ pixSW tp) ≡ mid
_ = refl

_ : src (∂ pixSW rt) ≡ mid
_ = refl

-- So the realisation has a path from the top of the upper pixel to the bottom
-- of the lower one, running down their two vertical sides through `mid`.
top bottom : V
top    = (1 , 0) , tt
bottom = (1 , 2) , tt

through : Path (∣ V , E , Sq ∣) (∣ top ∣₀) (∣ bottom ∣₀)
through = ∣ top ⇒ mid ∋ edge (inr (refl , tt)) ∣₁
        ∙ ∣ mid ⇒ bottom ∋ edge (inr (refl , tt)) ∣₁

-- In fact the realisation is contractible, which `Examples.ImageMatching`
-- shows with the Morse theorem.
isContr∣corner∣ : isContr ∣ V , E , Sq ∣
isContr∣corner∣ = EIM.Wedge.isContr∣wedge∣
