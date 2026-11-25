{-# OPTIONS --cubical --guardedness -WnoUnsupportedIndexedMatch --safe #-}

-- A full acyclic Morse matching on the cube complex of an arbitrary picture.
--
-- The rule is local — every cell decides on its partner by looking at the four
-- pixels around it — and it is greedy in the sense that a cell is left Critical
-- only when the two candidate partners it may point at are unavailable:
--
--   · every square is matched with its *top* edge (fullness in dimension two);
--   · a vertex is matched with the edge *below* it whenever that edge exists —
--     vertical edges are never the top of a square, so they are always free;
--   · failing that, it is matched with the edge to its *right*, provided that
--     edge is not already taken by the square underneath it, i.e. provided the
--     pixel to the south-east of the vertex is white;
--   · otherwise it is Critical.
--
-- Gradient paths therefore only ever move right and down, so acyclicity is a
-- matter of the picture being finite (`mPos` and `m₁` below are the measures
-- that go down along a path, and they are what makes the two flows terminate).
--
-- Reading the rule off, the Critical cells are exactly:
--
--   · the vertices whose only black neighbour is the pixel to their north-west
--     — the "south-east tips" of the picture — one of which sits on every
--     component, and
--   · the horizontal edges with a black pixel above, a white pixel below and a
--     black pixel to the south-west.
--
-- No vertical edge is ever Critical: the edge below a vertex exists exactly
-- when the vertex is matched downwards, and that is the first thing the rule
-- tries.
--
-- A filled rectangle, for instance, has a single Critical cell: the vertex at
-- its bottom right corner.
module ImageMatching where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Data.Bool hiding (_≤_ ; _≟_)
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded
open import Cubical.Relation.Nullary

open import Agda.Builtin.Char
open import Agda.Builtin.String

open import Prelude
import GraphMatching as GM
open import ComplexMatching
open import ImageComplex

private
  variable
    ℓ ℓ' : Level

--------------------------------------------------------------------------------
-- Booleans as propositions
--
-- The cells of a picture are cut out by boolean predicates, so proofs about
-- them are mostly a matter of taking `Bool→Type` of a formula apart and
-- putting it back together.

or-l : (b c : Bool) → Bool→Type b → Bool→Type (b or c)
or-l false c ()
or-l true  c _ = tt

or-r : (b c : Bool) → Bool→Type c → Bool→Type (b or c)
or-r false c h = h
or-r true  c _ = tt

or-elim : (b c : Bool) → Bool→Type (b or c) → Bool→Type b ⊎ Bool→Type c
or-elim false c h = inr h
or-elim true  c _ = inl tt

and-l : (b c : Bool) → Bool→Type (b and c) → Bool→Type b
and-l false c ()
and-l true  c _ = tt

and-r : (b c : Bool) → Bool→Type (b and c) → Bool→Type c
and-r false c ()
and-r true  c h = h

and-i : (b c : Bool) → Bool→Type b → Bool→Type c → Bool→Type (b and c)
and-i false c ()
and-i true  c _ h = h

not-i : (b : Bool) → ¬ Bool→Type b → Bool→Type (not b)
not-i false _  = tt
not-i true  ¬h = ¬h tt

not-elim : (b : Bool) → Bool→Type (not b) → ¬ Bool→Type b
not-elim false _ ()
not-elim true  () _

--------------------------------------------------------------------------------
-- Bounded quantification
--
-- A boolean predicate that computes to `true` on every number below `n` holds
-- below `n`; since a picture is finite, this is what turns a statement about
-- all of its cells into a single `refl`.

allB : ℕ → (ℕ → Bool) → Bool
allB zero    f = true
allB (suc n) f = f n and allB n f

allB→ : (n : ℕ) (f : ℕ → Bool) → Bool→Type (allB n f)
  → (k : ℕ) → k < n → Bool→Type (f k)
allB→ zero    f h k b = absurd (¬-<-zero b)
allB→ (suc n) f h k b with <-split b
... | inl k<n = allB→ n f (and-r (f n) (allB n f) h) k k<n
... | inr k≡n = subst (λ z → Bool→Type (f z)) (sym k≡n) (and-l (f n) (allB n f) h)

--------------------------------------------------------------------------------
-- Well-foundedness from a measure

-- a relation whose steps decrease a natural number is well-founded
module _ {A : Type ℓ} {R : A → A → Type ℓ'} (m : A → ℕ)
    (dec : {x y : A} → R x y → m x < m y) where

  private
    accFrom : (n : ℕ) (x : A) → m x < n → Acc R x
    accFrom zero    x b = absurd (¬-<-zero b)
    accFrom (suc n) x b = acc λ y r → accFrom n y (<≤-trans (dec r) (pred-≤-pred b))

  measureWF : WellFounded R
  measureWF x = accFrom (suc (m x)) x ≤-refl

--------------------------------------------------------------------------------
-- Odds and ends
--
-- Arithmetic of truncated subtraction, and the width of a picture.

private
  dbl : ℕ → ℕ
  dbl n = n + n

  dbl-< : {j k : ℕ} → j < k → dbl j < dbl k
  dbl-< p = <-+-< p p

  -- one step further down a truncated subtraction, as long as there is room
  ∸-suc-< : (n k : ℕ) → k < n → (n ∸ suc k) < (n ∸ k)
  ∸-suc-< zero    k       p = absurd (¬-<-zero p)
  ∸-suc-< (suc n) zero    p = ≤-refl
  ∸-suc-< (suc n) (suc k) p = ∸-suc-< n k (pred-≤-pred p)

  -- the width of the picture: the longest of its rows
  maxLen : List String → ℕ
  maxLen []       = 0
  maxLen (s ∷ ss) = max (length (primStringToList s)) (maxLen ss)


module Match (picture : List String) where

  -- `Image` proves the same things about the complex as `Complex` records, so
  -- the shared names are taken from the bundled complex.  Both are re-exported:
  -- opening `Match` is meant to be all a user of the matching needs.
  open Image picture public
    hiding (V-discrete ; E-isIrrefl ; E-isHProp ; Sq-isHProp ; ∂-inj)
  open Complex complex public

  --------------------------------------------------------------------------
  -- The picture is finite
  --
  -- Every black pixel lies in the first `N` rows and the first `W` columns —
  -- everything outside is white because `at` then returns its default.  These
  -- are the two bounds that make the gradient flows terminate.

  N W : ℕ
  N = length picture
  W = maxLen picture

  private
    row : ℕ → List Char
    row y = primStringToList (at "" picture y)

    at-out : {A : Type₀} (d : A) (as : List A) (n : ℕ) → length as ≤ n → at d as n ≡ d
    at-out d []       n       _  = refl
    at-out d (a ∷ as) zero    le = absurd (¬-<-zero le)
    at-out d (a ∷ as) (suc n) le = at-out d as n (pred-≤-pred le)

    at-len : (ss : List String) (y : ℕ)
      → length (primStringToList (at "" ss y)) ≤ maxLen ss
    at-len []       y       = zero-≤
    at-len (s ∷ ss) zero    = left-≤-max
    at-len (s ∷ ss) (suc y) = ≤-trans (at-len ss y) right-≤-max

    black-out-y : (x y : ℕ) → N ≤ y → black x y ≡ false
    black-out-y x y le =
        cong (λ s → primCharEquality '#' (at '.' (primStringToList s) x))
             (at-out "" picture y le)
      ∙ cong (primCharEquality '#') (at-out '.' [] x zero-≤)

    black-out-x : (x y : ℕ) → length (row y) ≤ x → black x y ≡ false
    black-out-x x y le = cong (primCharEquality '#') (at-out '.' (row y) x le)

  blackY : {x y : ℕ} → Bool→Type (black x y) → y < N
  blackY {x} {y} b with splitℕ-< y N
  ... | inl p  = p
  ... | inr q  = absurd (subst Bool→Type (black-out-y x y q) b)

  blackX : {x y : ℕ} → Bool→Type (black x y) → x < W
  blackX {x} {y} b with splitℕ-< x (length (row y))
  ... | inl p  = <≤-trans p (at-len picture y)
  ... | inr q  = absurd (subst Bool→Type (black-out-x x y q) b)

  -- A vertex is a lattice point of a black pixel, so it lies in the box one
  -- wider and one taller than the picture.  With `allB` this bounds any search
  -- over the cells of a concrete picture.
  vertexX : {x y : ℕ} → Bool→Type (vertexB x y) → x < suc W
  vertexY : {x y : ℕ} → Bool→Type (vertexB x y) → y < suc N

  private
    -- the same bounds for the pixels the edges of a vertex look at
    pxLeftY : (x y : ℕ) → Bool→Type (pxLeft x y) → y < N
    pxLeftY zero    y ()
    pxLeftY (suc x) y l = blackY l

    pxSWX : (x y : ℕ) → Bool→Type (pxSW x y) → x < suc W
    pxSWX zero    y ()
    pxSWX (suc x) y b = suc-≤-suc (blackX b)

    pxSWY : (x y : ℕ) → Bool→Type (pxSW x y) → y < suc N
    pxSWY zero    y ()
    pxSWY (suc x) y b = ≤-suc (blackY b)

    pxNEX : (x y : ℕ) → Bool→Type (pxNE x y) → x < suc W
    pxNEX x zero    ()
    pxNEX x (suc y) b = ≤-suc (blackX b)

    pxNEY : (x y : ℕ) → Bool→Type (pxNE x y) → y < suc N
    pxNEY x zero    ()
    pxNEY x (suc y) b = suc-≤-suc (blackY b)

    pxNWX : (x y : ℕ) → Bool→Type (pxNW x y) → x < suc W
    pxNWX zero    y       ()
    pxNWX (suc x) zero    ()
    pxNWX (suc x) (suc y) b = suc-≤-suc (blackX b)

    pxNWY : (x y : ℕ) → Bool→Type (pxNW x y) → y < suc N
    pxNWY zero    y       ()
    pxNWY (suc x) zero    ()
    pxNWY (suc x) (suc y) b = suc-≤-suc (blackY b)

  vertexX {x} {y} v with or-elim (black x y) (vRest x y) v
  ... | inl b = ≤-suc (blackX b)
  ... | inr w with or-elim (pxSW x y) (vRest' x y) w
  ...         | inl b = pxSWX x y b
  ...         | inr w' with or-elim (pxNE x y) (pxNW x y) w'
  ...                  | inl b = pxNEX x y b
  ...                  | inr b = pxNWX x y b

  vertexY {x} {y} v with or-elim (black x y) (vRest x y) v
  ... | inl b = ≤-suc (blackY b)
  ... | inr w with or-elim (pxSW x y) (vRest' x y) w
  ...         | inl b = pxSWY x y b
  ...         | inr w' with or-elim (pxNE x y) (pxNW x y) w'
  ...                  | inl b = pxNEY x y b
  ...                  | inr b = pxNWY x y b

  -- A boolean property of positions that computes to `true` at every point of
  -- that box which is a vertex holds at every vertex.  The premise is a closed
  -- boolean, so instantiating it is a `refl` — this is how a statement about
  -- all the cells of a concrete picture gets checked.
  allVertices : (f : ℕ → ℕ → Bool)
    → Bool→Type (allB (suc W) (λ x → allB (suc N) (λ y → not (vertexB x y) or f x y)))
    → (u : V) → Bool→Type (f (fst (pos u)) (snd (pos u)))
  allVertices f h ((x , y) , v) with or-elim (not (vertexB x y)) (f x y) box
    where
    box : Bool→Type (not (vertexB x y) or f x y)
    box = allB→ (suc N) (λ y' → not (vertexB x y') or f x y')
            (allB→ (suc W) (λ z → allB (suc N) (λ y' → not (vertexB z y') or f z y'))
                   h x (vertexX v))
            y (vertexY v)
  ... | inl ¬v = absurd (not-elim (vertexB x y) ¬v v)
  ... | inr q  = q

  private

    vEdgesY : (x y : ℕ) → Bool→Type (vEdgesB x y) → y < N
    vEdgesY x y d with or-elim (black x y) (pxLeft x y) d
    ... | inl b = blackY b
    ... | inr l = pxLeftY x y l

    pxAboveX : (x y : ℕ) → Bool→Type (pxAbove x y) → x < W
    pxAboveX x zero    ()
    pxAboveX x (suc y) a = blackX a

    hEdgesX : (x y : ℕ) → Bool→Type (hEdgesB x y) → x < W
    hEdgesX x y r with or-elim (black x y) (pxAbove x y) r
    ... | inl b = blackX b
    ... | inr a = pxAboveX x y a

  --------------------------------------------------------------------------
  -- Positions

  -- a vertex is determined by its position: being one is a proposition
  V≡ : {u v : V} → pos u ≡ pos v → u ≡ v
  V≡ = Σ≡Prop (λ _ → isPropBool→Type)

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

  private

    -- the endpoints of an edge determine which of the two kinds it is
    edgeDn : {u v : V} → E u v → pos v ≡ down (pos u) → Bool→Type (vEdgesP (pos u))
    edgeDn (edge (inl (q , _))) p = absurd (right≢down _ (sym q ∙ p))
    edgeDn (edge (inr (_ , d))) _ = d

  --------------------------------------------------------------------------
  -- The two vertices a vertex may be matched with are vertices
  --
  -- If the edge below (x , y) exists then the pixel to the north-east or the
  -- one to the north-west of (x , suc y) is black, and symmetrically for the
  -- edge to the right.

  private
    vtxDnNW : (x y : ℕ) → Bool→Type (pxLeft x y) → Bool→Type (vertexB x (suc y))
    vtxDnNW zero    y ()
    vtxDnNW (suc x) y l =
      or-r (black (suc x) (suc y)) (vRest (suc x) (suc y))
        (or-r (pxSW (suc x) (suc y)) (vRest' (suc x) (suc y))
          (or-r (pxNE (suc x) (suc y)) (pxNW (suc x) (suc y)) l))

    vtxDn : (x y : ℕ) → Bool→Type (vEdgesB x y) → Bool→Type (vertexB x (suc y))
    vtxDn x y d with or-elim (black x y) (pxLeft x y) d
    ... | inl b =
      or-r (black x (suc y)) (vRest x (suc y))
        (or-r (pxSW x (suc y)) (vRest' x (suc y))
          (or-l (pxNE x (suc y)) (pxNW x (suc y)) b))
    ... | inr l = vtxDnNW x y l

    vtxRtNW : (x y : ℕ) → Bool→Type (pxAbove x y) → Bool→Type (vertexB (suc x) y)
    vtxRtNW x zero    ()
    vtxRtNW x (suc y) a =
      or-r (black (suc x) (suc y)) (vRest (suc x) (suc y))
        (or-r (pxSW (suc x) (suc y)) (vRest' (suc x) (suc y))
          (or-r (pxNE (suc x) (suc y)) (pxNW (suc x) (suc y)) a))

    vtxRt : (x y : ℕ) → Bool→Type (hEdgesB x y) → Bool→Type (vertexB (suc x) y)
    vtxRt x y r with or-elim (black x y) (pxAbove x y) r
    ... | inl b =
      or-r (black (suc x) y) (vRest (suc x) y)
        (or-l (pxSW (suc x) y) (vRest' (suc x) y) b)
    ... | inr a = vtxRtNW x y a

  --------------------------------------------------------------------------
  -- The matching of the vertices
  --
  -- `μΣ` computes the partner of a vertex *together with the reason* it was
  -- chosen, so that every later proof can read that reason off `μspec` instead
  -- of redoing the case analysis.  The last disjunct of `MuStep` is the one
  -- that keeps the matching a matching: a vertex takes the edge to its right
  -- only when the pixel below that edge is white, and then that edge is not
  -- the top edge of any square.

  -- a matched vertex goes with the edge below it, or — and then there is no
  -- edge below it — with the one to its right
  MuStep : V → V → Type₀
  MuStep u v =
      ((E u v) × (pos v ≡ down (pos u)))
    ⊎ ((E u v) × (pos v ≡ right (pos u))
              × (¬ Bool→Type (pix (pos u)))
              × (¬ Bool→Type (vEdgesP (pos u))))

  -- and a Critical one has neither: no edge below it, and no edge to its right
  -- that the square below that edge does not already claim
  MuCrit₀ : V → Type₀
  MuCrit₀ u = (¬ Bool→Type (vEdgesP (pos u)))
           × (Bool→Type (hEdgesP (pos u)) → Bool→Type (pix (pos u)))

  MuSpec : V → V → Type₀
  MuSpec u v = ((pos v ≡ pos u) × MuCrit₀ u) ⊎ MuStep u v

  μΣ : (u : V) → Σ[ v ∈ V ] MuSpec u v
  μΣ ((x , y) , h) with DecBool→Type {a = vEdgesB x y}
  ... | yes d = ((x , suc y) , vtxDn x y d)
              , inr (inl (edge (inr (refl , d)) , refl))
  ... | no ¬d with DecBool→Type {a = hEdgesB x y} | DecBool→Type {a = black x y}
  ...         | yes r | no ¬b = ((suc x , y) , vtxRt x y r)
                              , inr (inr (edge (inl (refl , r)) , refl , ¬b , ¬d))
  ...         | yes r | yes b = ((x , y) , h) , inl (refl , ¬d , λ _ → b)
  ...         | no ¬r | _     = ((x , y) , h) , inl (refl , ¬d , λ r → absurd (¬r r))

  μ : V → V
  μ u = fst (μΣ u)

  μspec : (u : V) → MuSpec u (μ u)
  μspec u = snd (μΣ u)

  --------------------------------------------------------------------------
  -- The matching of the squares
  --
  -- Every square goes with its top edge.  Two distinct squares have distinct
  -- top edges — the top edge determines the north-west corner of the pixel,
  -- and `Sq` pins the other three corners down to it.

  ν : Squares → Side
  ν _ = tp

  μ̂-inj : {s s' : Squares} → ∂ s tp ≡ ∂ s' tp → s ≡ s'
  μ̂-inj {a  , b  , c  , d  , t  , bo  , l  , r  , pb  , pc  , pd  , px }
        {a' , b' , c' , d' , t' , bo' , l' , r' , pb' , pc' , pd' , px'} p =
    ΣPathP (pa , ΣPathP (pbv , ΣPathP (pcv , ΣPathP (pdv ,
      isProp→PathP (λ i → SquareOn-isHProp (pa i) (pbv i) (pcv i) (pdv i)) _ _))))
    where
    pa : a ≡ a'
    pa = cong fst p

    pbv : b ≡ b'
    pbv = cong (λ z → fst (snd z)) p

    pcv : c ≡ c'
    pcv = V≡ (pc ∙ cong down (cong pos pa) ∙ sym pc')

    pdv : d ≡ d'
    pdv = V≡ (pd ∙ cong (λ z → right (down z)) (cong pos pa) ∙ sym pd')

  --------------------------------------------------------------------------
  -- No edge is matched twice
  --
  -- An edge matched with a square is the top edge of a black pixel; that is
  -- exactly the situation the third disjunct of `MuSpec` excludes.

  isUpTop : Edges → Type₀
  isUpTop e = Σ[ s ∈ Squares ] ∂ s tp ≡ e

  upBlack : {e : Edges} → isUpTop e → Bool→Type (pix (pos (src e)))
  upBlack ((a , b , c , d , t , bo , l , r , pb , pc , pd , px) , q) =
    subst (λ z → Bool→Type (pix (pos (src z)))) q px

  upRight : {e : Edges} → isUpTop e → pos (tgt e) ≡ right (pos (src e))
  upRight ((a , b , c , d , t , bo , l , r , pb , pc , pd , px) , q) =
    subst (λ z → pos (tgt z) ≡ right (pos (src z))) q pb

  up∩dn : (e : Edges) → isUpTop e → ¬ (μ (src e) ≡ tgt e)
  up∩dn e up dn with μspec (src e)
  ... | inl (p , _)       = ≢right (pos (src e)) (sym p ∙ toRight)
    where
    toRight : pos (μ (src e)) ≡ right (pos (src e))
    toRight = cong pos dn ∙ upRight up
  ... | inr (inl (_ , p)) = right≢down (pos (src e)) (sym toRight ∙ p)
    where
    toRight : pos (μ (src e)) ≡ right (pos (src e))
    toRight = cong pos dn ∙ upRight up
  ... | inr (inr (_ , _ , ¬b , _)) = ¬b (upBlack up)

  --------------------------------------------------------------------------
  -- Deciding whether an edge caps a square
  --
  -- The matching datum asks for this; for a picture it is decidable because an
  -- edge caps a square exactly when it is horizontal with a black pixel below
  -- it, and that square is then the pixel itself.

  -- conversely, a horizontal edge with a black pixel below it caps the square
  -- of that very pixel
  upTop : (e : Edges) → pos (tgt e) ≡ right (pos (src e))
    → Bool→Type (pix (pos (src e))) → isUpTop e
  upTop (u , v , f) h b =
    cell (fst (pos u)) (snd (pos u)) b ,
    ΣPathP (V≡ refl , ΣPathP (V≡ (sym h) ,
      isProp→PathP (λ i → E-isHProp _ _) _ _))

  isUp? : (e : Edges) → Dec (isUpTop e)
  isUp? (u , v , edge (inr (q , _))) =
    no λ up → right≢down (pos u) (sym (upRight up) ∙ q)
  isUp? e@(u , v , edge (inl (h , hb))) with DecBool→Type {a = pix (pos u)}
  ... | no ¬b = no λ up → ¬b (upBlack up)
  ... | yes b = yes (upTop e h b)

  --------------------------------------------------------------------------
  -- The matching

  matchingData : MatchingData complex
  matchingData = record
    { μ₀ = μ ; μ₁ = ν ; μ̂₁-inj = μ̂-inj ; up∩dn = up∩dn ; isUp? = isUp? }

  -- dimension zero is the graph development, verbatim …
  open GM.Paths graph μ using (isCrit₀ ; Crit₀ ; _ᵥ ; _⇝_ ; end ; step ; acyclic)
  -- … and dimension one the one of `ComplexMatching`
  open GradientPaths complex matchingData using (isUp ; isDn ; _⇒₁_ ; _<₁_ ; acyclic₁)

  --------------------------------------------------------------------------
  -- Acyclicity in dimension zero
  --
  -- A matched vertex moves right or down, and both moves shrink `mPos`; the
  -- flow is then a recursion on that measure, given as fuel.

  mPos : Pos → ℕ
  mPos (x , y) = (N ∸ y) + (W ∸ x)

  m₀ : V → ℕ
  m₀ u = mPos (pos u)

  private
    mPos-down : (x y : ℕ) → Bool→Type (vEdgesB x y) → mPos (x , suc y) < mPos (x , y)
    mPos-down x y d = <-+k (∸-suc-< N y (vEdgesY x y d))

    mPos-right : (x y : ℕ) → Bool→Type (hEdgesB x y) → mPos (suc x , y) < mPos (x , y)
    mPos-right x y r = <-k+ (∸-suc-< W x (hEdgesX x y r))

    downDec : (u v : V) → E u v → pos v ≡ down (pos u) → m₀ v < m₀ u
    downDec ((x , y) , _) v e p =
      subst (λ q → mPos q < mPos (x , y)) (sym p) (mPos-down x y (edgeDn e p))

    rightDec : (u v : V) → Bool→Type (hEdgesP (pos u)) → pos v ≡ right (pos u)
      → m₀ v < m₀ u
    rightDec ((x , y) , _) v r p =
      subst (λ q → mPos q < mPos (x , y)) (sym p) (mPos-right x y r)

    edgeRt : {u v : V} → E u v → pos v ≡ right (pos u) → Bool→Type (hEdgesP (pos u))
    edgeRt (edge (inl (_ , r))) _ = r
    edgeRt (edge (inr (q , _))) p = absurd (right≢down _ (sym p ∙ q))

    stepEdges : {u v : V} → MuStep u v → E u v
    stepEdges (inl (e , _))     = e
    stepEdges (inr (e , _ , _ , _)) = e

    -- the partner of a non-Critical vertex is strictly closer to the bottom
    -- right corner of the picture
    μdec : (u : V) → MuStep u (μ u) → m₀ (μ u) < m₀ u
    μdec u (inl (e , p))     = downDec u (μ u) e p
    μdec u (inr (e , p , _ , _)) = rightDec u (μ u) (edgeRt e p) p

    flowFuel : (n : ℕ) (u : V) → m₀ u ≤ n → Σ[ c ∈ Crit₀ ] u ⇝ c ᵥ
    flowFuel zero u le with μspec u
    ... | inl (p , _) = (u , V≡ p) , end (V≡ p) refl
    ... | inr q = absurd (¬-<-zero (<≤-trans (μdec u q) le))
    flowFuel (suc n) u le with μspec u
    ... | inl (p , _) = (u , V≡ p) , end (V≡ p) refl
    ... | inr q =
      let rec = flowFuel n (μ u) (pred-≤-pred (<≤-trans (μdec u q) le))
      in fst rec , step {u , μ u , stepEdges q} refl (snd rec)

  flow : acyclic
  flow u = flowFuel (m₀ u) u ≤-refl

  --------------------------------------------------------------------------
  -- Acyclicity in dimension one
  --
  -- A gradient step leaves the top edge of a black pixel through one of the
  -- other three sides of that pixel: through the bottom, which is one row
  -- further down, or through the left or the right, which are vertical.  The
  -- measure below therefore drops at every step: rows are counted twice, so
  -- that a horizontal edge still outweighs the two vertical edges beside it.

  m₁ : Edges → ℕ
  m₁ (u , v , edge (inl _)) = suc (dbl (N ∸ snd (pos u)))
  m₁ (u , v , edge (inr _)) =      dbl (N ∸ snd (pos u))

  private
    m₁-hor : (e : Edges) → pos (tgt e) ≡ right (pos (src e))
      → m₁ e ≡ suc (dbl (N ∸ snd (pos (src e))))
    m₁-hor (u , v , edge (inl _))       h = refl
    m₁-hor (u , v , edge (inr (q , _))) h = absurd (right≢down (pos u) (sym h ∙ q))

    m₁-ver : (e : Edges) → pos (tgt e) ≡ down (pos (src e))
      → m₁ e ≡ dbl (N ∸ snd (pos (src e)))
    m₁-ver (u , v , edge (inl (q , _))) h = absurd (right≢down (pos u) (sym q ∙ h))
    m₁-ver (u , v , edge (inr _))       h = refl

    -- leaving a square through a side other than the top one
    exitDec : (s : Squares) (i : Side) → ¬ i ≡ tp → m₁ (∂ s i) < m₁ (∂ s tp)
    exitDec s tp ¬i = absurd (¬i refl)
    exitDec s@(a , b , c , d , t , bo , l , r , pb , pc , pd , px) bt ¬i =
      subst2 (λ j k → j < k) (sym eqbt) (sym eqtp) ineq
      where
      eqtp : m₁ (∂ s tp) ≡ suc (dbl (N ∸ snd (pos a)))
      eqtp = m₁-hor (∂ s tp) pb

      eqbt : m₁ (∂ s bt) ≡ suc (dbl (N ∸ snd (pos c)))
      eqbt = m₁-hor (∂ s bt) (pd ∙ sym (cong right pc))

      -- the pixel is black, so there is a row below its top one
      ineq : suc (dbl (N ∸ snd (pos c))) < suc (dbl (N ∸ snd (pos a)))
      ineq = subst (λ z → suc (dbl (N ∸ z)) < suc (dbl (N ∸ snd (pos a))))
               (sym (cong snd pc))
               (suc-≤-suc (dbl-< (∸-suc-< N (snd (pos a)) (blackY px))))
    exitDec s@(a , b , c , d , t , bo , l , r , pb , pc , pd , px) lf ¬i =
      subst2 (λ j k → j < k) (sym (m₁-ver (∂ s lf) pc)) (sym (m₁-hor (∂ s tp) pb)) ≤-refl
    exitDec s@(a , b , c , d , t , bo , l , r , pb , pc , pd , px) rt ¬i =
      subst2 (λ j k → j < k) (sym eqrt) (sym (m₁-hor (∂ s tp) pb)) ≤-refl
      where
      eqrt : m₁ (∂ s rt) ≡ dbl (N ∸ snd (pos a))
      eqrt = m₁-ver (∂ s rt) (pd ∙ sym (cong down pb)) ∙ cong (λ z → dbl (N ∸ z)) (cong snd pb)

    stepDec : {e f : Edges} → e ⇒₁ f → m₁ f < m₁ e
    stepDec (s , p , i , ¬i , q) =
      subst2 (λ ff ee → m₁ ff < m₁ ee) q p (exitDec s i ¬i)

  flow₁ : acyclic₁
  flow₁ = measureWF m₁ (λ {x} {y} r → stepDec r)

  --------------------------------------------------------------------------
  -- … and that is a full acyclic Morse matching on the picture

  matching : 2FullMatching complex
  matching = matchingData , flow , flow₁

  --------------------------------------------------------------------------
  -- Reading the Critical cells off the picture
  --
  -- These are what turn the local rule into a statement about a *given*
  -- picture: they bound the Critical cells by boolean conditions on the pixels
  -- around them, which `allVertices` then checks on the whole picture at once.

  -- every vertical edge is matched with its source …
  μdown : (u v : V) → pos v ≡ down (pos u) → Bool→Type (vEdgesP (pos u)) → μ u ≡ v
  μdown u v p d with μspec u
  ... | inl (_ , ¬d , _)           = absurd (¬d d)
  ... | inr (inl (_ , q))          = V≡ (q ∙ sym p)
  ... | inr (inr (_ , _ , _ , ¬d)) = absurd (¬d d)

  -- … and a horizontal edge with a white pixel below it is matched with its
  -- source too, unless the source has an edge below it to take instead
  μright : (u v : V) → pos v ≡ right (pos u) → Bool→Type (hEdgesP (pos u))
    → ¬ Bool→Type (pix (pos u)) → (μ u ≡ v) ⊎ Bool→Type (vEdgesP (pos u))
  μright u v p r ¬b with μspec u
  ... | inl (_ , _ , f)           = absurd (¬b (f r))
  ... | inr (inl (e , q))         = inr (edgeDn e q)
  ... | inr (inr (_ , q , _ , _)) = inl (V≡ (q ∙ sym p))

  -- a Critical vertex has no edge below it, and the edge to its right — if
  -- there is one — is the top edge of the black pixel below it
  CritVertex : (u : V) → μ u ≡ u → MuCrit₀ u
  CritVertex u p with μspec u
  ... | inl (_ , c)               = c
  ... | inr (inl (_ , q))         = absurd (≢down  (pos u) (sym (cong pos p) ∙ q))
  ... | inr (inr (_ , q , _ , _)) = absurd (≢right (pos u) (sym (cong pos p) ∙ q))

  -- a Critical edge is horizontal, with a white pixel below it and — since its
  -- source must have had an edge below it to prefer — a black one to its
  -- south-west
  CritEdges : (e : Edges) → ¬ isDn e → ¬ isUp e
    → (pos (tgt e) ≡ right (pos (src e)))
    × Bool→Type (hEdgesP (pos (src e)))
    × (¬ Bool→Type (pix (pos (src e))))
    × Bool→Type (vEdgesP (pos (src e)))
  CritEdges (u , v , edge (inr (q , d))) ¬dn ¬up = absurd (¬dn (μdown u v q d))
  CritEdges (u , v , edge (inl (h , r))) ¬dn ¬up = h , r , ¬b , vd
    where
    ¬b : ¬ Bool→Type (pix (pos u))
    ¬b b = ¬up (upTop (u , v , edge (inl (h , r))) h b)

    vd : Bool→Type (vEdgesP (pos u))
    vd with μright u v h r ¬b
    ... | inl m = absurd (¬dn m)
    ... | inr d = d


