{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

module Examples.Book where

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

data V : Type where
  spL spR : V          -- the two ends of the spine
  pgL pgR : ℕ → V      -- the two lower corners of page n

data E : V → V → Type where
  spine : E spL spR
  left  : (n : ℕ) → E spL (pgL n)
  right : (n : ℕ) → E spR (pgR n)
  base  : (n : ℕ) {m : ℕ} → n ≡ m → E (pgL n) (pgR m)

-- being the bottom edge of a page
isBase : {u v : V} → E u v → Type
isBase (base _ _) = Unit
isBase _ = ⊥

-- `Sq t bo l r` takes its boundary in the order top, bottom, left, right.  The
-- page number is *not* repeated across the four indices: a square is the spine
-- on top, a base edge below, and whatever two edges join them — the constraint
-- that all four belong to the same page is carried by `isBase bo` and by the
-- types of `l` and `r`, and no clause of what follows ever has to unify one
-- occurrence of `n` with another (which is axiom K, and unavailable here).
data Sq : {x y z w : V} → E x y → E z w → E x z → E y w → Type where
  page : {z w : V} (bo : E z w) (l : E spL z) (r : E spR w) → isBase bo
       → Sq spine bo l r

open Cells V E Sq

pageCell : ℕ → Squares
pageCell n = spL , spR , pgL n , pgR n
           , spine , base n refl , left n , right n
           , page (base n refl) (left n) (right n) tt

-- all pages share their top edge — it is the same 1-cell, not a copy of it —
-- and share nothing else
_ : ∂ (pageCell 3) tp ≡ ∂ (pageCell 7) tp
_ = refl

_ : ∂ (pageCell 3) bt ≡ (pgL 3 , pgR 3 , base 3 refl)
_ = refl

--------------------------------------------------------------------------------
-- Telling vertices apart
--
-- The usual encode-decode: `Code x y` is `⊥` for distinct constructors, so a
-- path between two of them is a contradiction, and `ℕ`-equality for a matching
-- pair, so `encode` is also the injectivity of `pgL` and `pgR`.

Code : V → V → Type
Code spL spL = Unit
Code spR spR = Unit
Code (pgL m) (pgL n) = m ≡ n
Code (pgR m) (pgR n) = m ≡ n
Code _ _ = ⊥

codeRefl : (x : V) → Code x x
codeRefl spL = tt
codeRefl spR = tt
codeRefl (pgL n) = refl
codeRefl (pgR n) = refl

encode : {x y : V} → x ≡ y → Code x y
encode {x} p = subst (Code x) p (codeRefl x)

V-discrete : Discrete V
V-discrete spL spL = yes refl
V-discrete spR spR = yes refl
V-discrete (pgL m) (pgL n) with discreteℕ m n
... | yes p = yes (cong pgL p)
... | no ¬p = no λ q → ¬p (encode q)
V-discrete (pgR m) (pgR n) with discreteℕ m n
... | yes p = yes (cong pgR p)
... | no ¬p = no λ q → ¬p (encode q)
V-discrete spL spR = no encode
V-discrete spL (pgL n) = no encode
V-discrete spL (pgR n) = no encode
V-discrete spR spL = no encode
V-discrete spR (pgL n) = no encode
V-discrete spR (pgR n) = no encode
V-discrete (pgL m) spL = no encode
V-discrete (pgL m) spR = no encode
V-discrete (pgL m) (pgR n) = no encode
V-discrete (pgR m) spL = no encode
V-discrete (pgR m) spR = no encode
V-discrete (pgR m) (pgL n) = no encode

--------------------------------------------------------------------------------
-- … and the complex

E-isIrrefl : (u : V) → ¬ (E u u)
E-isIrrefl u ()

E-isHProp : (u v : V) → isHProp (E u v)
E-isHProp _ _ spine spine = refl
E-isHProp _ _ (left n) (left _) = refl
E-isHProp _ _ (right n) (right _) = refl
E-isHProp _ _ (base n p) (base _ q) = cong (λ z → base n z) (isSetℕ _ _ p q)

isBase-isHProp : {u v : V} (e : E u v) → isHProp (isBase e)
isBase-isHProp spine = isProp⊥
isBase-isHProp (left n) = isProp⊥
isBase-isHProp (right n) = isProp⊥
isBase-isHProp (base n p) = isPropUnit

-- the two ends of a base edge, and the page they belong to
baseEnds : {u v : V} (e : E u v) → isBase e → Σ[ k ∈ ℕ ] (u ≡ pgL k) × (v ≡ pgR k)
baseEnds (base n p) _ = n , refl , cong pgR (sym p)

Sq-isHProp : {x y z w : V} (t : E x y) (bo : E z w) (l : E x z) (r : E y w)
  → isHProp (Sq t bo l r)
Sq-isHProp _ _ _ _ (page bo l r h) (page _ _ _ h') =
  cong (page bo l r) (isBase-isHProp bo h h')

-- the four sides of a page are pairwise distinct: it is enough to look at
-- their endpoints, and `page` forces the top one to run spL ⇒ spR
∂-inj : (s : Squares) {i j : Side} → ∂ s i ≡ ∂ s j → i ≡ j
∂-inj s {tp} {tp} _ = refl
∂-inj s {bt} {bt} _ = refl
∂-inj s {lf} {lf} _ = refl
∂-inj s {rt} {rt} _ = refl
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {tp} {bt} q =
  absurd (encode (cong src q ∙ fst (snd (baseEnds bo h))))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {tp} {lf} q =
  absurd (encode (cong tgt q ∙ fst (snd (baseEnds bo h))))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {tp} {rt} q =
  absurd (encode (cong src q))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {bt} {tp} q =
  absurd (encode (sym (fst (snd (baseEnds bo h))) ∙ cong src q))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {bt} {lf} q =
  absurd (encode (sym (fst (snd (baseEnds bo h))) ∙ cong src q))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {bt} {rt} q =
  absurd (encode (sym (fst (snd (baseEnds bo h))) ∙ cong src q))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {lf} {tp} q =
  absurd (encode (sym (fst (snd (baseEnds bo h))) ∙ cong tgt q))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {lf} {bt} q =
  absurd (encode (cong src q ∙ fst (snd (baseEnds bo h))))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {lf} {rt} q =
  absurd (encode (cong src q))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {rt} {tp} q =
  absurd (encode (cong src q))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {rt} {bt} q =
  absurd (encode (cong src q ∙ fst (snd (baseEnds bo h))))
∂-inj (_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) {rt} {lf} q =
  absurd (encode (cong src q))

graph : Graph V E
graph = record
  { V-discrete = V-discrete ; E-isIrrefl = E-isIrrefl ; E-isHProp = E-isHProp }

complex : Complex V E Sq
complex = record { graph = graph ; Sq-isHProp = Sq-isHProp ; ∂-inj = ∂-inj }

open Complex complex using (SquareOn-isHProp)

--------------------------------------------------------------------------------
-- The matching
--
--   · `ν` matches every page with its left edge,
--   · `μ` matches `spL` with the spine and `pgL n` with the base of page n.
--
-- What is left over is `spR`, the corners `pgR n`, and the edges `right n`.

μ : V → V
μ spL = spR
μ spR = spR
μ (pgL n) = pgR n
μ (pgR n) = pgR n

ν : Squares → Side
ν _ = lf

-- `μ̂ s` is `∂ s (ν s)`, here always the left edge; an edge capping a page
-- therefore runs from `spL` to a near corner, which is all the following two
-- lemmas record
isUpLeft : Edges → Type
isUpLeft e = Σ[ s ∈ Squares ] ∂ s lf ≡ e

upSrc : {e : Edges} → isUpLeft e → src e ≡ spL
upSrc ((_ , _ , _ , _ , _ , _ , _ , _ , page _ _ _ _) , q) = sym (cong src q)

upTgt : {e : Edges} → isUpLeft e → Σ[ k ∈ ℕ ] tgt e ≡ pgL k
upTgt ((_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) , q) =
  let (k , zk , _) = baseEnds bo h in k , sym (cong tgt q) ∙ zk

-- a page is determined by its left edge: that edge names the near corner, the
-- corner names the page, and the rest of the cell is a proposition
μ̂-inj : {s s' : Squares} → ∂ s lf ≡ ∂ s' lf → s ≡ s'
μ̂-inj {_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h}
      {_ , _ , _ , _ , _ , _ , _ , _ , page bo' l' r' h'} q =
  ΣPathP (refl , ΣPathP (refl , ΣPathP (cong tgt q , ΣPathP (w≡w' ,
    isProp→PathP (λ i → SquareOn-isHProp _ _ _ _) _ _))))
  where
  z≡z' : _
  z≡z' = cong tgt q
  w≡w' : _
  w≡w' = let (k , zk , wk) = baseEnds bo h
             (k' , zk' , wk') = baseEnds bo' h'
         in wk ∙ cong pgR (encode (sym zk ∙ z≡z' ∙ zk')) ∙ sym wk'

-- the three kinds of edge that cap no page
¬up-spine : ¬ isUpLeft (spL , spR , spine)
¬up-spine up = encode (snd (upTgt up))

¬up-base : {u v : V} (e : E u v) → isBase e → ¬ isUpLeft (u , v , e)
¬up-base e h up = encode (sym (fst (snd (baseEnds e h))) ∙ upSrc up)

¬up-fromR : {v : V} (e : E spR v) → ¬ isUpLeft (spR , v , e)
¬up-fromR e up = encode (upSrc up)

-- an edge capping a page starts at `spL`, and `spL` is matched with the spine,
-- not with a corner
up∩dn : (e : Edges) → isUpLeft e → ¬ (μ (src e) ≡ tgt e)
up∩dn e up dn =
  encode (sym (cong μ (upSrc up)) ∙ dn ∙ snd (upTgt up))

-- an edge caps a page exactly when it is a left edge, and then the page is the
-- one it names
isUp? : (e : Edges) → Dec (isUpLeft e)
isUp? (_ , _ , spine) = no ¬up-spine
isUp? (_ , _ , left n) = yes (pageCell n , refl)
isUp? (_ , _ , right n) = no (¬up-fromR (right n))
isUp? (_ , _ , base n p) = no (¬up-base (base n p) tt)

matchingData : MatchingData complex
matchingData = record
  { μ₀ = μ ; μ₁ = ν ; μ̂₁-inj = μ̂-inj ; up∩dn = up∩dn ; isUp? = isUp? }

open GM.Paths graph μ using (Crit₀ ; _ᵥ ; _⇝_ ; end ; step ; acyclic)
open GradientPaths complex matchingData using (isUp ; _⇒₁_ ; _<₁_ ; acyclic₁ ; upStep)

--------------------------------------------------------------------------------
-- … is acyclic in both dimensions
--
-- In dimension zero the flow is one step long: `spL` slides along the spine to
-- `spR`, and `pgL n` along the base to `pgR n`, and those two are Critical.

flow : acyclic
flow spL = (spR , refl) , step {spL , spR , spine} refl (end refl refl)
flow spR = (spR , refl) , end refl refl
flow (pgL n) = (pgR n , refl) , step {pgL n , pgR n , base n refl} refl (end refl refl)
flow (pgR n) = (pgR n , refl) , end refl refl

-- In dimension one it is one step long too: only a left edge caps a square, and
-- a step out of one leaves through another side of that page — the spine, the
-- base, or the right edge — none of which caps anything.

accNoUp : (e : Edges) → ¬ isUp e → Acc _<₁_ e
accNoUp e ¬up = acc λ f stp → absurd (¬up (upStep stp))

stepFromLeft : (n : ℕ) (f : Edges) → (spL , pgL n , left n) ⇒₁ f → ¬ isUp f
stepFromLeft n f ((_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) , _ , tp , _ , q) =
  subst (λ g → ¬ isUp g) q ¬up-spine
stepFromLeft n f ((_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) , _ , bt , _ , q) =
  subst (λ g → ¬ isUp g) q (¬up-base bo h)
stepFromLeft n f ((_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) , _ , lf , ¬lf , _) =
  absurd (¬lf refl)
stepFromLeft n f ((_ , _ , _ , _ , _ , _ , _ , _ , page bo l r h) , _ , rt , _ , q) =
  subst (λ g → ¬ isUp g) q (¬up-fromR r)

flow₁ : acyclic₁
flow₁ (_ , _ , spine) = accNoUp _ ¬up-spine
flow₁ (_ , _ , base n p) = accNoUp _ (¬up-base (base n p) tt)
flow₁ (_ , _ , right n) = accNoUp _ (¬up-fromR (right n))
flow₁ (_ , _ , left n) = acc λ f stp → accNoUp f (stepFromLeft n f stp)

matching : 2FullMatching complex
matching = matchingData , flow , flow₁

module Mo = Morse complex matching
-- the Morse complex's gradient paths are the ones of the collapsed complex
module Mo⁻ = Mo.Mo⁻

--------------------------------------------------------------------------------
-- The Morse complex is the infinite star
--
-- Its vertices are `spR` and the far corners, its edges the `right n`, and the
-- gradient flow puts each of them where the picture says: `right n` runs from
-- the Critical vertex `spR` to the Critical vertex `pgR n`.

data Vtx : Type where
  ⋆ : Vtx
  leaf : ℕ → Vtx

data Arr : Vtx → Vtx → Type where
  rib : (n : ℕ) → Arr ⋆ (leaf n)

isPropArr : (i j : Vtx) → isHProp (Arr i j)
isPropArr _ _ (rib n) (rib _) = refl

β : Mo.Crit₀
β = spR , refl

δ : ℕ → Mo.Crit₀
δ n = pgR n , refl

ribEdges : ℕ → Edges
ribEdges n = spR , pgR n , right n

ribCrit₀ : (n : ℕ) → Mo.Edges⁻
ribCrit₀ n = spR , pgR n , right n , ¬up-fromR (right n)

arr : (n : ℕ) → Mo⁻.Crit₁ β (δ n)
arr n = ribCrit₀ n , encode , Mo⁻.end refl refl , Mo⁻.end refl refl

F : Mo.Crit₀ → Vtx
F (spL , pf) = absurd (encode pf)
F (spR , _) = ⋆
F (pgL n , pf) = absurd (encode pf)
F (pgR n , _) = leaf n

G : Vtx → Mo.Crit₀
G ⋆ = β
G (leaf n) = δ n

S : (x : Vtx) → F (G x) ≡ x
S ⋆ = refl
S (leaf n) = refl

R : (κ : Mo.Crit₀) → G (F κ) ≡ κ
R (spL , pf) = absurd (encode pf)
R (spR , pf) = Σ≡Prop Mo.isCritIsHProp refl
R (pgL n , pf) = absurd (encode pf)
R (pgR n , pf) = Σ≡Prop Mo.isCritIsHProp refl

G₁ : (i j : Vtx) → Arr i j → Mo⁻.Crit₁ (G i) (G j)
G₁ _ _ (rib n) = arr n

-- Every Critical edge is a `right n`: the spine and the bases are matched
-- downwards, the left edges upwards.  Its endpoints are then read off by
-- flowing, and `spR` and `pgR n` are Critical, so both flows stand still.
F₁ : (κ ρ : Mo.Crit₀) → Mo⁻.Crit₁ κ ρ → Arr (F κ) (F ρ)
F₁ κ ρ ((_ , _ , spine , _) , ¬dn , _ , _) = absurd (¬dn refl)
F₁ κ ρ ((_ , _ , left n , ¬up) , _ , _ , _) = absurd (¬up (pageCell n , refl))
F₁ κ ρ ((_ , _ , base n p , _) , ¬dn , _ , _) = absurd (¬dn (cong pgR p))
F₁ κ ρ ((_ , _ , right n , _) , _ , p , q) =
  subst2 Arr (sym (cong F κ≡β)) (sym (cong F ρ≡δ)) (rib n)
  where
  κ≡β : κ ≡ β
  κ≡β = Σ≡Prop Mo.isCritIsHProp (Mo⁻.sinkUniq (κ ᵥ) spR p (Mo⁻.end refl refl))
  ρ≡δ : ρ ≡ δ n
  ρ≡δ = Σ≡Prop Mo.isCritIsHProp (Mo⁻.sinkUniq (ρ ᵥ) (pgR n) q (Mo⁻.end refl refl))

--------------------------------------------------------------------------------
-- Both round-trips are propositions
--
-- Two Critical edges with the same endpoints are the same one: the flow of the
-- target names the page, and everything else about a Critical edge — that it is
-- matched neither way, and where its ends flow to — is a proposition.

isPropCrit₁ᴹ : {κ ρ : Mo.Crit₀} → isHProp (Mo⁻.Crit₁ κ ρ)
isPropCrit₁ᴹ ((_ , _ , spine , _) , ¬dn , _ , _) _ = absurd (¬dn refl)
isPropCrit₁ᴹ ((_ , _ , left n , ¬up) , _ , _ , _) _ = absurd (¬up (pageCell n , refl))
isPropCrit₁ᴹ ((_ , _ , base n p , _) , ¬dn , _ , _) _ = absurd (¬dn (cong pgR p))
isPropCrit₁ᴹ ((_ , _ , right n , _) , _ , _ , _) ((_ , _ , spine , _) , ¬dn , _ , _) =
  absurd (¬dn refl)
isPropCrit₁ᴹ ((_ , _ , right n , _) , _ , _ , _) ((_ , _ , left m , ¬up) , _ , _ , _) =
  absurd (¬up (pageCell m , refl))
isPropCrit₁ᴹ ((_ , _ , right n , _) , _ , _ , _) ((_ , _ , base m p , _) , ¬dn , _ , _) =
  absurd (¬dn (cong pgR p))
isPropCrit₁ᴹ {κ} {ρ} ((_ , _ , right n , _) , _ , p , q) ((_ , _ , right m , _) , _ , p' , q') =
  ΣPathP (Mo.ₑ-inj (cong ribEdges n≡m)
         , ΣPathP ( isProp→PathP (λ _ → isProp¬ _) _ _
                  , isProp→PathP (λ i → isProp× (Mo⁻.⇝IsHProp κ) (Mo⁻.⇝IsHProp ρ)) _ _))
  where
  n≡m : n ≡ m
  n≡m = encode (sym (Mo⁻.sinkUniq (ρ ᵥ) (pgR n) q (Mo⁻.end refl refl))
                ∙ Mo⁻.sinkUniq (ρ ᵥ) (pgR m) q' (Mo⁻.end refl refl))

S₁ : (i j : Vtx) (x : Arr i j)
   → PathP (λ k → Arr (S i k) (S j k)) (F₁ (G i) (G j) (G₁ i j x)) x
S₁ i j x = toPathP (isPropArr i j _ x)

R₁ : (κ ρ : Mo.Crit₀) (f : Mo⁻.Crit₁ κ ρ)
   → PathP (λ k → Mo⁻.Crit₁ (R κ k) (R ρ k)) (G₁ (F κ) (F ρ) (F₁ κ ρ f)) f
R₁ κ ρ f = toPathP (isPropCrit₁ᴹ {κ} {ρ}
  (transport (λ k → Mo⁻.Crit₁ (R κ k) (R ρ k)) (G₁ (F κ) (F ρ) (F₁ κ ρ f))) f)

Crit₁ᴹ≡Arr : GR.∣ Mo.Crit₀ , Mo⁻.Crit₁ ∣ ≡ GR.∣ Vtx , Arr ∣
Crit₁ᴹ≡Arr = GR.isoReal F F₁ G G₁ S S₁ R R₁

--------------------------------------------------------------------------------
-- The star is a tree, and the book is a point

ι : Unit → Vtx
ι tt = ⋆

p⋆ : Path (GR.∣ Vtx , Arr ∣) (GR.∣ ⋆ ∣₀) (GR.∣ ⋆ ∣₀)
p⋆ = refl

pleaf : (n : ℕ) → Path (GR.∣ Vtx , Arr ∣) (GR.∣ ⋆ ∣₀) (GR.∣ leaf n ∣₀)
pleaf n = p⋆ ∙ GR.∣ ⋆ ⇒ leaf n ∋ rib n ∣₁

root : Vtx → Unit
root _ = tt

rootIsRoot : (r : Unit) → root (ι r) ≡ r
rootIsRoot tt = refl

rootPath : (v : Vtx) → Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι (root v) ∣₀) (GR.∣ v ∣₀)
rootPath ⋆ = p⋆
rootPath (leaf n) = pleaf n

contrEdge : {i j : Vtx} (x : Arr i j)
  → Σ[ α ∈ root i ≡ root j ]
      PathP (λ k → Path (GR.∣ Vtx , Arr ∣) (GR.∣ ι (α k) ∣₀) (GR.∣ i ⇒ j ∋ x ∣₁ k))
            (rootPath i) (rootPath j)
contrEdge (rib n) = refl , compPath-filler p⋆ GR.∣ ⋆ ⇒ leaf n ∋ rib n ∣₁

∣Arr∣≡Unit : GR.∣ Vtx , Arr ∣ ≡ Unit
∣Arr∣≡Unit = ForestCollapse Unit ι root rootIsRoot rootPath contrEdge

bookIsUnit : ∣ V , E , Sq ∣ ≡ Unit
bookIsUnit = Mo.MorseTheorem ∙ Crit₁ᴹ≡Arr ∙ ∣Arr∣≡Unit
