{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

module Examples.3DCube where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool renaming (_≟_ to _≟B_)
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.S2
open import Cubical.Relation.Nullary

open import Prelude
import GraphMatching as GM
open GM using (Graph)
open import ComplexMatching
open import CType2

--------------------------------------------------------------------------------
-- The cells

data V : Type where
  v000 v100 v010 v110 v001 v101 v011 v111 : V

data E : V → V → Type where
  x₀₀ : E v000 v100
  x₁₀ : E v010 v110
  x₀₁ : E v001 v101
  x₁₁ : E v011 v111
  y₀₀ : E v000 v010
  y₁₀ : E v100 v110
  y₀₁ : E v001 v011
  y₁₁ : E v101 v111
  z₀₀ : E v000 v001
  z₁₀ : E v100 v101
  z₀₁ : E v010 v011
  z₁₁ : E v110 v111

-- The five faces of the cube other than the lid.  `Sq⁻ t bo l r` takes its
-- boundary in the order top, bottom, left, right, and every edge below occurs
-- in exactly two of the six faces — `x₀₁ x₁₁ y₀₁ y₁₁`, the four edges of the
-- lid, in only one of these five.
data Sq⁻ : {a b c d : V} → E a b → E c d → E a c → E b d → Type where
  bot   : Sq⁻ x₀₀ x₁₀ y₀₀ y₁₀     -- z = 0
  front : Sq⁻ x₀₀ x₀₁ z₀₀ z₁₀     -- y = 0
  back  : Sq⁻ x₁₀ x₁₁ z₀₁ z₁₁     -- y = 1
  left  : Sq⁻ y₀₀ y₀₁ z₀₀ z₀₁     -- x = 0
  right : Sq⁻ y₁₀ y₁₁ z₁₀ z₁₁     -- x = 1

-- … and the cube itself: those five, and the lid.
data Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type where
  face : {a b c d : V} {t : E a b} {bo : E c d} {l : E a c} {r : E b d}
       → Sq⁻ t bo l r → Sq t bo l r
  top  : Sq x₀₁ x₁₁ y₀₁ y₁₁       -- z = 1

∂I³ : Type
∂I³ = ∣ V , E , Sq ∣

D : Type
D = ∣ V , E , Sq⁻ ∣

-- the realised cells of the disk
ed : {u v : V} → E u v → Path D ∣ u ∣₀ ∣ v ∣₀
ed {u} {v} e = ∣ u ⇒ v ∋ e ∣₁

fc : {a b c d : V} {t : E a b} {bo : E c d} {l : E a c} {r : E b d}
   → Sq⁻ t bo l r → Square (ed t) (ed bo) (ed l) (ed r)
fc {t = t} {bo} {l} {r} s = ∣ t , bo , l , r ∋ s ∣₂

--------------------------------------------------------------------------------
-- Three sides of a square, contracted
--
-- If a point `w` is joined to three of the four corners of a square in a way
-- that is compatible with three of its sides, then the fourth side and the
-- filler are determined: they are the centre of a contractible type, namely
-- the singleton at the top side in the family "paths from `w` over the i-th
-- slice of the square".  This is `ComplexMorse.contrBot` with the point `w`
-- carried along, and it is all that dimension two costs below.

module _ {A : Type} (w : A) where

  Fill : {a b c d : A} {t : a ≡ b} {bo : c ≡ d} {l : a ≡ c} {r : b ≡ d}
    (sq : Square t bo l r)
    {pa : w ≡ a} {pb : w ≡ b} {pc : w ≡ c} {pd : w ≡ d}
    (qt : PathP (λ j → w ≡ t j) pa pb)
    (ql : PathP (λ i → w ≡ l i) pa pc)
    (qr : PathP (λ i → w ≡ r i) pb pd)
    → Σ[ qb ∈ PathP (λ j → w ≡ bo j) pc pd ]
        PathP (λ i → PathP (λ j → w ≡ sq i j) (ql i) (qr i)) qt qb
  Fill sq qt ql qr =
    isContrSinglP (λ i → PathP (λ j → w ≡ sq i j) (ql i) (qr i)) qt .fst

--------------------------------------------------------------------------------
-- The disk is contractible
--
-- Everything is contracted to `v000`.  The seven edges
--
--     x₀₀  y₀₀  y₁₀  z₀₀  z₁₀  z₀₁  z₁₁
--
-- form a spanning tree pointing away from it, and each is contracted by the
-- filler of the composite that defines the path to its target — this is
-- `Examples.Trees` verbatim.  The remaining five edges are the four edges of
-- the lid and `x₁₀`, and each of them is the bottom side of one of the five
-- squares: `Fill` contracts the edge and fills the square in one stroke.
-- The order matters only in that `back` uses the contraction of `x₁₀`, which
-- comes from `bot`.

pt : D
pt = ∣ v000 ∣₀

p000 : pt ≡ ∣ v000 ∣₀
p000 = refl
p100 : pt ≡ ∣ v100 ∣₀
p100 = p000 ∙ ed x₀₀
p010 : pt ≡ ∣ v010 ∣₀
p010 = p000 ∙ ed y₀₀
p110 : pt ≡ ∣ v110 ∣₀
p110 = p100 ∙ ed y₁₀
p001 : pt ≡ ∣ v001 ∣₀
p001 = p000 ∙ ed z₀₀
p101 : pt ≡ ∣ v101 ∣₀
p101 = p100 ∙ ed z₁₀
p011 : pt ≡ ∣ v011 ∣₀
p011 = p010 ∙ ed z₀₁
p111 : pt ≡ ∣ v111 ∣₀
p111 = p110 ∙ ed z₁₁

qx₀₀ : PathP (λ i → pt ≡ ed x₀₀ i) p000 p100
qx₀₀ = compPath-filler p000 (ed x₀₀)
qy₀₀ : PathP (λ i → pt ≡ ed y₀₀ i) p000 p010
qy₀₀ = compPath-filler p000 (ed y₀₀)
qy₁₀ : PathP (λ i → pt ≡ ed y₁₀ i) p100 p110
qy₁₀ = compPath-filler p100 (ed y₁₀)
qz₀₀ : PathP (λ i → pt ≡ ed z₀₀ i) p000 p001
qz₀₀ = compPath-filler p000 (ed z₀₀)
qz₁₀ : PathP (λ i → pt ≡ ed z₁₀ i) p100 p101
qz₁₀ = compPath-filler p100 (ed z₁₀)
qz₀₁ : PathP (λ i → pt ≡ ed z₀₁ i) p010 p011
qz₀₁ = compPath-filler p010 (ed z₀₁)
qz₁₁ : PathP (λ i → pt ≡ ed z₁₁ i) p110 p111
qz₁₁ = compPath-filler p110 (ed z₁₁)

-- the five collapses: each names the contraction of one more edge …
Fbot   = Fill pt (fc bot)   qx₀₀ qy₀₀ qy₁₀
qx₁₀   = Fbot .fst
Ffront = Fill pt (fc front) qx₀₀ qz₀₀ qz₁₀
qx₀₁   = Ffront .fst
Fback  = Fill pt (fc back)  qx₁₀ qz₀₁ qz₁₁
qx₁₁   = Fback .fst
Fleft  = Fill pt (fc left)  qy₀₀ qz₀₀ qz₀₁
qy₀₁   = Fleft .fst
Fright = Fill pt (fc right) qy₁₀ qz₁₀ qz₁₁
qy₁₁   = Fright .fst

-- … and, in its second component, fills the square that contracted it.
contr : (x : D) → pt ≡ x
contr ∣ v000 ∣₀ = p000
contr ∣ v100 ∣₀ = p100
contr ∣ v010 ∣₀ = p010
contr ∣ v110 ∣₀ = p110
contr ∣ v001 ∣₀ = p001
contr ∣ v101 ∣₀ = p101
contr ∣ v011 ∣₀ = p011
contr ∣ v111 ∣₀ = p111
contr (∣ v000 ⇒ v100 ∋ x₀₀ ∣₁ i) = qx₀₀ i
contr (∣ v010 ⇒ v110 ∋ x₁₀ ∣₁ i) = qx₁₀ i
contr (∣ v001 ⇒ v101 ∋ x₀₁ ∣₁ i) = qx₀₁ i
contr (∣ v011 ⇒ v111 ∋ x₁₁ ∣₁ i) = qx₁₁ i
contr (∣ v000 ⇒ v010 ∋ y₀₀ ∣₁ i) = qy₀₀ i
contr (∣ v100 ⇒ v110 ∋ y₁₀ ∣₁ i) = qy₁₀ i
contr (∣ v001 ⇒ v011 ∋ y₀₁ ∣₁ i) = qy₀₁ i
contr (∣ v101 ⇒ v111 ∋ y₁₁ ∣₁ i) = qy₁₁ i
contr (∣ v000 ⇒ v001 ∋ z₀₀ ∣₁ i) = qz₀₀ i
contr (∣ v100 ⇒ v101 ∋ z₁₀ ∣₁ i) = qz₁₀ i
contr (∣ v010 ⇒ v011 ∋ z₀₁ ∣₁ i) = qz₀₁ i
contr (∣ v110 ⇒ v111 ∋ z₁₁ ∣₁ i) = qz₁₁ i
contr (∣ _ , _ , _ , _ ∋ bot ∣₂ i j)   = Fbot .snd i j
contr (∣ _ , _ , _ , _ ∋ front ∣₂ i j) = Ffront .snd i j
contr (∣ _ , _ , _ , _ ∋ back ∣₂ i j)  = Fback .snd i j
contr (∣ _ , _ , _ , _ ∋ left ∣₂ i j)  = Fleft .snd i j
contr (∣ _ , _ , _ , _ ∋ right ∣₂ i j) = Fright .snd i j

isContrD : isContr D
isContrD = pt , contr

--------------------------------------------------------------------------------
-- Gluing a square onto a type
--
-- `Attach A t bo l r` is `A` with one more square glued along the four paths
-- `t bo l r` — the lid, once the disk is built.  The data it is glued along is
-- four points and four paths between them, which is `AData`.

data Attach (A : Type) {a b c d : A}
    (t : a ≡ b) (bo : c ≡ d) (l : a ≡ c) (r : b ≡ d) : Type where
  inc  : A → Attach A t bo l r
  cell : Square (λ i → inc (t i)) (λ i → inc (bo i))
                (λ i → inc (l i)) (λ i → inc (r i))

AData : Type → Type
AData A = Σ[ a ∈ A ] Σ[ b ∈ A ] Σ[ c ∈ A ] Σ[ d ∈ A ]
          Σ[ t ∈ a ≡ b ] Σ[ bo ∈ c ≡ d ] Σ[ l ∈ a ≡ c ] (b ≡ d)

Att : (A : Type) → AData A → Type
Att A (a , b , c , d , t , bo , l , r) = Attach A t bo l r

-- In a contractible type there is nothing to glue along: the corners and the
-- edges are contractible choices too.
isContrAData : {A : Type} → isContr A → isContr (AData A)
isContrAData cA =
  isOfHLevelΣ 0 cA λ a → isOfHLevelΣ 0 cA λ b →
  isOfHLevelΣ 0 cA λ c → isOfHLevelΣ 0 cA λ d →
  isOfHLevelΣ 0 (isContr→isContrPath cA a b) λ _ →
  isOfHLevelΣ 0 (isContr→isContrPath cA c d) λ _ →
  isOfHLevelΣ 0 (isContr→isContrPath cA a c) λ _ →
  isContr→isContrPath cA b d

trivial : AData Unit
trivial = tt , tt , tt , tt , refl , refl , refl , refl

-- So the whole gluing datum can be transported to the trivial one: the type
-- along `isContr→≡Unit`, and the eight cells along the contractibility of
-- `AData`, which holds all the way along that path.
AttachContr : {A : Type} → isContr A → (dat : AData A) → Att A dat ≡ Att Unit trivial
AttachContr {A} cA dat i = Att (q i) (dp i)
  where
  q : A ≡ Unit
  q = isContr→≡Unit cA

  cq : (i : I) → isContr (q i)
  cq i = transp (λ j → isContr (q (i ∧ j))) (~ i) cA

  dp : PathP (λ i → AData (q i)) dat trivial
  dp = isProp→PathP (λ i → isContr→isProp (isContrAData (cq i))) dat trivial

-- and a point with a square glued to it along nothing is the sphere, on the
-- nose: `inc tt` is `base` and `cell` is `surf`.
AttUnit≡S² : Att Unit trivial ≡ S²
AttUnit≡S² = isoToPath (iso F G S R) where
  F : Att Unit trivial → S²
  F (inc tt) = base
  F (cell i j) = surf i j
  G : S² → Att Unit trivial
  G base = inc tt
  G (surf i j) = cell i j
  S : (x : S²) → F (G x) ≡ x
  S base = refl
  S (surf i j) = refl
  R : (x : Att Unit trivial) → G (F x) ≡ x
  R (inc tt) = refl
  R (cell i j) = refl

--------------------------------------------------------------------------------
-- The cube is the disk with the lid glued back on
--
-- Both maps are the identity on cells: the five faces of `Sq` that come from
-- `Sq⁻` are the disk's, and the lid is `cell`.  Nothing is composed, so both
-- round-trips are `refl`.

lid : AData D
lid = ∣ v001 ∣₀ , ∣ v101 ∣₀ , ∣ v011 ∣₀ , ∣ v111 ∣₀ , ed x₀₁ , ed x₁₁ , ed y₀₁ , ed y₁₁

∂I³≡Att : ∂I³ ≡ Att D lid
∂I³≡Att = isoToPath (iso F G S R) where
  F : ∂I³ → Att D lid
  F ∣ v ∣₀ = inc ∣ v ∣₀
  F (∣ u ⇒ v ∋ e ∣₁ i) = inc (∣ u ⇒ v ∋ e ∣₁ i)
  F (∣ t , bo , l , r ∋ face s ∣₂ i j) = inc (∣ t , bo , l , r ∋ s ∣₂ i j)
  F (∣ _ , _ , _ , _ ∋ top ∣₂ i j) = cell i j

  ι : D → ∂I³
  ι ∣ v ∣₀ = ∣ v ∣₀
  ι (∣ u ⇒ v ∋ e ∣₁ i) = ∣ u ⇒ v ∋ e ∣₁ i
  ι (∣ t , bo , l , r ∋ s ∣₂ i j) = ∣ t , bo , l , r ∋ face s ∣₂ i j

  G : Att D lid → ∂I³
  G (inc x) = ι x
  G (cell i j) = ∣ x₀₁ , x₁₁ , y₀₁ , y₁₁ ∋ top ∣₂ i j

  Fι : (x : D) → F (ι x) ≡ inc x
  Fι ∣ v ∣₀ = refl
  Fι (∣ u ⇒ v ∋ e ∣₁ i) = refl
  Fι (∣ t , bo , l , r ∋ s ∣₂ i j) = refl

  S : (x : Att D lid) → F (G x) ≡ x
  S (inc x) = Fι x
  S (cell i j) = refl

  R : (x : ∂I³) → G (F x) ≡ x
  R ∣ v ∣₀ = refl
  R (∣ u ⇒ v ∋ e ∣₁ i) = refl
  R (∣ t , bo , l , r ∋ face s ∣₂ i j) = refl
  R (∣ _ , _ , _ , _ ∋ top ∣₂ i j) = refl

--------------------------------------------------------------------------------
-- The theorem

∣cube∣≡S² : ∣ V , E , Sq ∣ ≡ S²
∣cube∣≡S² = ∂I³≡Att ∙ AttachContr isContrD lid ∙ AttUnit≡S²

--------------------------------------------------------------------------------
-- The cube is a complex
--
-- Nothing above asked the cells to satisfy anything: `CType2` realises
-- a bare `Cube'`.  They do satisfy the axioms of `ComplexMatching.Complex`,
-- though — vertices with decidable equality, edges irreflexive and
-- propositional, squares propositional, and the four sides of every square
-- pairwise distinct — so the cube is a legitimate input to the matching
-- machinery, and the collapse above is not a way of dodging it.
--
-- It carries no full matching, and cannot: a full acyclic matching feeds
-- `ComplexMorse.Morse.MorseTheorem`, which rewrites the realisation as one of a
-- complex with no squares — the realisation of a graph, hence a groupoid.  By
-- `∣cube∣≡S²` that groupoid would be `S²`, whose π₂ is `ℤ`.  So the six squares
-- cannot all be cancelled; the collapse above, which spends five of them and
-- leaves the lid standing, is as far as one gets.

--------------------------------------------------------------------------------
-- Vertices are discrete
--
-- A vertex *is* its triple of coordinates, and `Bool × Bool × Bool` is
-- discrete, so this is the encode-decode of `ComplexMatching.Side` again.

co : V → Bool × Bool × Bool
co v000 = false , false , false
co v100 = true  , false , false
co v010 = false , true  , false
co v110 = true  , true  , false
co v001 = false , false , true
co v101 = true  , false , true
co v011 = false , true  , true
co v111 = true  , true  , true

fr : Bool × Bool × Bool → V
fr (false , false , false) = v000
fr (true  , false , false) = v100
fr (false , true  , false) = v010
fr (true  , true  , false) = v110
fr (false , false , true)  = v001
fr (true  , false , true)  = v101
fr (false , true  , true)  = v011
fr (true  , true  , true)  = v111

fr-co : (v : V) → fr (co v) ≡ v
fr-co v000 = refl
fr-co v100 = refl
fr-co v010 = refl
fr-co v110 = refl
fr-co v001 = refl
fr-co v101 = refl
fr-co v011 = refl
fr-co v111 = refl

co-inj : {u v : V} → co u ≡ co v → u ≡ v
co-inj {u} {v} p = sym (fr-co u) ∙ cong fr p ∙ fr-co v

V-discrete : Discrete V
V-discrete u v =
  mapDec co-inj (λ ¬p q → ¬p (cong co q))
    (discreteΣ _≟B_ (λ _ → discreteΣ _≟B_ (λ _ → _≟B_)) (co u) (co v))

-- the three coordinates separately: two vertices that differ in one of them
-- are distinct, which is how every inequality below is discharged
cx cy cz : V → Bool
cx v = co v .fst
cy v = co v .snd .fst
cz v = co v .snd .snd

≢co : (f : V → Bool) {u v : V} → ¬ f u ≡ f v → ¬ u ≡ v
≢co f h p = h (cong f p)

--------------------------------------------------------------------------------
-- The graph, and the squares
--
-- Every edge runs between two *different* vertices, and for each pair there is
-- at most one edge and at most one square with a given boundary, so the two
-- h-propositionality proofs are all `refl`.

E-isIrrefl : (u : V) → ¬ (E u u)
E-isIrrefl u ()

E-isHProp : (u v : V) → isProp (E u v)
E-isHProp _ _ x₀₀ x₀₀ = refl
E-isHProp _ _ x₁₀ x₁₀ = refl
E-isHProp _ _ x₀₁ x₀₁ = refl
E-isHProp _ _ x₁₁ x₁₁ = refl
E-isHProp _ _ y₀₀ y₀₀ = refl
E-isHProp _ _ y₁₀ y₁₀ = refl
E-isHProp _ _ y₀₁ y₀₁ = refl
E-isHProp _ _ y₁₁ y₁₁ = refl
E-isHProp _ _ z₀₀ z₀₀ = refl
E-isHProp _ _ z₁₀ z₁₀ = refl
E-isHProp _ _ z₀₁ z₀₁ = refl
E-isHProp _ _ z₁₁ z₁₁ = refl

graph : Graph V E
graph = record
  { V-discrete = V-discrete ; E-isIrrefl = E-isIrrefl ; E-isHProp = E-isHProp }

Sq⁻-isHProp : {a b c d : V} (t : E a b) (bo : E c d) (l : E a c) (r : E b d)
  → isProp (Sq⁻ t bo l r)
Sq⁻-isHProp _ _ _ _ bot   bot   = refl
Sq⁻-isHProp _ _ _ _ front front = refl
Sq⁻-isHProp _ _ _ _ back  back  = refl
Sq⁻-isHProp _ _ _ _ left  left  = refl
Sq⁻-isHProp _ _ _ _ right right = refl

-- the lid is not one of the five faces of the disk: no `Sq⁻` has its boundary
Sq-isHProp : {a b c d : V} (t : E a b) (bo : E c d) (l : E a c) (r : E b d)
  → isProp (Sq t bo l r)
Sq-isHProp _ _ _ _ (face s) (face s') = cong face (Sq⁻-isHProp _ _ _ _ s s')
Sq-isHProp _ _ _ _ top top = refl

open Cells V E Sq

--------------------------------------------------------------------------------
-- The four sides of a square are pairwise distinct
--
-- On a square  a — b   the sides are tp = (a,b), bt = (c,d), lf = (a,c) and
--              |   |   rt = (b,d), so three inequalities between the corners
--              c — d   separate all six pairs: `a ≢ b` splits tp from rt and lf
-- from rt, `a ≢ c` splits tp from bt and bt from lf, and `b ≢ c` splits tp from
-- lf and bt from rt.  Each split reads off one endpoint of the two edges.

∂-inj₄ : {a b c d : V} (s : SquareOn a b c d)
  → ¬ a ≡ b → ¬ a ≡ c → ¬ b ≡ c
  → {i j : Side} → ∂ (a , b , c , d , s) i ≡ ∂ (a , b , c , d , s) j → i ≡ j
∂-inj₄ s ab ac bc {tp} {tp} q = refl
∂-inj₄ s ab ac bc {bt} {bt} q = refl
∂-inj₄ s ab ac bc {lf} {lf} q = refl
∂-inj₄ s ab ac bc {rt} {rt} q = refl
∂-inj₄ s ab ac bc {tp} {bt} q = absurd (ac (cong src q))
∂-inj₄ s ab ac bc {tp} {lf} q = absurd (bc (cong tgt q))
∂-inj₄ s ab ac bc {tp} {rt} q = absurd (ab (cong src q))
∂-inj₄ s ab ac bc {bt} {tp} q = absurd (ac (sym (cong src q)))
∂-inj₄ s ab ac bc {bt} {lf} q = absurd (ac (sym (cong src q)))
∂-inj₄ s ab ac bc {bt} {rt} q = absurd (bc (sym (cong src q)))
∂-inj₄ s ab ac bc {lf} {tp} q = absurd (bc (sym (cong tgt q)))
∂-inj₄ s ab ac bc {lf} {bt} q = absurd (ac (cong src q))
∂-inj₄ s ab ac bc {lf} {rt} q = absurd (ab (cong src q))
∂-inj₄ s ab ac bc {rt} {tp} q = absurd (ab (sym (cong src q)))
∂-inj₄ s ab ac bc {rt} {bt} q = absurd (bc (cong src q))
∂-inj₄ s ab ac bc {rt} {lf} q = absurd (ab (sym (cong src q)))

-- for each of the six faces, the corners a, b, c differ in one coordinate
∂-inj : (s : Squares) {i j : Side} → ∂ s i ≡ ∂ s j → i ≡ j
∂-inj (_ , _ , _ , _ , s@(_ , _ , _ , _ , face bot)) =
  ∂-inj₄ s (≢co cx false≢true) (≢co cy false≢true) (≢co cx true≢false)
∂-inj (_ , _ , _ , _ , s@(_ , _ , _ , _ , face front)) =
  ∂-inj₄ s (≢co cx false≢true) (≢co cz false≢true) (≢co cx true≢false)
∂-inj (_ , _ , _ , _ , s@(_ , _ , _ , _ , face back)) =
  ∂-inj₄ s (≢co cx false≢true) (≢co cz false≢true) (≢co cx true≢false)
∂-inj (_ , _ , _ , _ , s@(_ , _ , _ , _ , face left)) =
  ∂-inj₄ s (≢co cy false≢true) (≢co cz false≢true) (≢co cy true≢false)
∂-inj (_ , _ , _ , _ , s@(_ , _ , _ , _ , face right)) =
  ∂-inj₄ s (≢co cy false≢true) (≢co cz false≢true) (≢co cy true≢false)
∂-inj (_ , _ , _ , _ , s@(_ , _ , _ , _ , top)) =
  ∂-inj₄ s (≢co cx false≢true) (≢co cy false≢true) (≢co cx true≢false)

complex : Complex V E Sq
complex = record { graph = graph ; Sq-isHProp = Sq-isHProp ; ∂-inj = ∂-inj }
