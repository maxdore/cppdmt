{-# OPTIONS --cubical --guardedness --safe #-}

-- This artefact accompanies
-- "Studying the Topology of Images with Discrete Morse Theory in Cubical Agda"

-- The code has been typechecked with Agda in version 2.6.4.3. and the Cubical
-- library in version 0.7. All files compile with the --cubical and --safe flags,


open import Prelude

-- Geometric realisations of semi-cubical types of dimensions 1 and 2
open import CType1
open import CType2

-- The graph lemmas from Section 3
open import GraphForest
open import GraphBouquet

-- Discrete Morse theory for Graphs
open import GraphMatching
open import GraphMorse

-- Discrete Morse theory for Complexes
open import ComplexMatching
open import ComplexMorse

-- The results about digital images for Section 6
open import ImageComplex
open import ImageMatching
open import ImageMorse

-- Example Graphs and Complexes and their properties
open import Examples.SquareCollapse
open import Examples.Book
open import Examples.Torus
open import Examples.3DCube
open import Examples.Bouquets
open import Examples.Trees
open import Examples.Line
open import Examples.Two
open import Examples.ImageMatching
open import Examples.Corner
open import Examples.Voevodsky
open import Examples.Mug
