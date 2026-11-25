{-# OPTIONS --cubical --guardedness --safe #-}
module ComplexMorse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels renaming (isSet→SquareP to isHSet→SquareP)
open import Cubical.Foundations.Path
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded

open import Prelude
open import CType2
open import ComplexMatching
import CType1 as GR
import GraphMatching as GM
import GraphMorse as GMo

private
  variable
    ℓ : Level



-- First we collapse the squares using the μ₁ part of the matching

module MorseSquares {V : Type ℓ} {E : V → V → Type ℓ} {Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type ℓ}
  (K : Complex V E Sq) (M : 2FullMatching K) where
  open Complex K public
  private
    m    = fst M
    acy₀ = fst (snd M)
    acy₁ = snd (snd M)

  open GradientPaths K (fst M) public
  open GM.Matching graph (MatchingData.μ₀ m , acy₀) public
    using ( _Crit? ; _⇒ᵐ?_ ; sink ; _⇝sink ; sinkUniq ; sinkUniqᶜ
          ; ⇝IsHProp ; ⇝IsHPropS ; Crit₁IsHSet ; comp⇝ ; _⇝?_ ; module compE )


  --------------------------------------------------------------------------
  -- The graph the squares collapse onto
  --
  -- Cancelling every square against the face `μ₁` picks for it leaves the
  -- graph G⁻ of edges capping no square.  `μ` is still a matching on it — a
  -- gradient path only ever steps along an edge matched with its source, and
  -- such an edge caps no square — so dimension zero is the graph development
  -- applied to G⁻, verbatim.

  E⁻ : V → V → Type ℓ
  E⁻ u v = Σ[ f ∈ E u v ] ¬ isUp (u , v , f)


  -- `Edges⁻` is not just `Edges` with a side condition, instead, the ¬ isUp
  -- witness is part of the edge, which makes `P⁻.Crit₁` usable as the Morse
  -- complex's edge type below.
  module Edge⁻ = GM.Edge E⁻
  open Edge⁻ public using () renaming (Edges to Edges⁻)

  -- the underlying edge of the complex
  _ₑ : Edges⁻ → Edges
  (u , v , f , _) ₑ = u , v , f
  infix 100 _ₑ

  -- … and it determines the edge of the collapsed complex, the `¬ isUp`
  -- witness riding along being a proposition
  ₑ-inj : {e f : Edges⁻} → e ₑ ≡ f ₑ → e ≡ f
  ₑ-inj p = ΣPathP (cong fst p , ΣPathP (cong (λ z → fst (snd z)) p ,
    isProp→PathP (λ i → isPropΣ (E-isHProp _ _) (λ _ → isProp¬ _)) _ _))

  G⁻ : GM.Graph V E⁻
  G⁻ = record { V-discrete = V-discrete
    ; E-isIrrefl = λ u (f , _) → E-isIrrefl u f
    ; E-isHProp  = λ u v → isPropΣ (E-isHProp u v) λ _ → isProp¬ _
    }

  module P⁻ = GM.Paths G⁻ μ₀

  -- A gradient path of the complex never leaves G⁻: `up∩dn` says an edge
  -- matched with its source caps no square.
  ⇝⁻ : {u v : V} → u ⇝ v → P⁻._⇝_ u v
  ⇝⁻ (end c p) = P⁻.end c p
  ⇝⁻ (step {u , w , f} m p) =
    P⁻.step {u , w , f , (λ up → up∩dn (u , w , f) up m)} m (⇝⁻ p)

  M⁻ : GM.Matching G⁻
  M⁻ = μ₀ , λ u → sink u , ⇝⁻ (u ⇝sink)

  module Mo⁻ = GMo.Morse G⁻ M⁻


  SquareCollapse : ∣ V , E , Sq ∣ ≡ ∣ V , E⁻ , (λ _ _ _ _ → ⊥*) ∣
  SquareCollapse = isoToPath (iso ϕ ι sec ret) where

    ⇝⁻← : {u v : V} → P⁻._⇝_ u v → u ⇝ v
    ⇝⁻← (P⁻.end c p) = end c p
    ⇝⁻← (P⁻.step {u , w , f , _} m p) = step {u , w , f} m (⇝⁻← p)


    -- The promised refinement of the inherited `Crit₁`: dimension zero can only
    -- ask that an edge is unmatched *downwards*, whereas here an edge capping a
    -- square must be discarded too.
    Crit₁ᴹ→Crit₁ : {c d : Crit₀} → P⁻.Crit₁ c d → Crit₁ c d
    Crit₁ᴹ→Crit₁ ((u , v , f , _) , ¬dn , p , q) =
      (u , v , f) , ¬dn , ⇝⁻← p , ⇝⁻← q

    -- The Morse complex itself, realised.  Its 2-cell relation is empty: a full
    -- matching leaves no Critical squares.  (Written inline rather than as a
    -- named `NoSq`, which Agda cannot elaborate here — it would have to invert
    -- the non-injective `Crit₁ᴹ` to recover the four corners.)
    -- ∣Morse∣ : Type ℓ
    -- ∣Morse∣ = ∣ Crit₀ , Crit₁ᴹ , (λ _ _ _ _ → ⊥*) ∣

    --------------------------------------------------------------------------
    -- Collapsing the squares
    --
    -- The matching is full on squares, so the collapse happens in two
    -- independent halves: every square cancels against the face `μ₁` picks for
    -- it, and every non-Critical vertex cancels against the edge `μ` picks for
    -- it.  The second half is dimension zero and is the graph development
    -- verbatim; only the first is new, and it is carried out here.
    --
    -- What is left after cancelling the squares is the graph of edges capping
    -- no square.

    wf₁ : acyclic₁
    wf₁ = snd (snd M)

    -- The sides of a square, in a realisation
    --
    -- All of the two-dimensional bookkeeping is stated for an arbitrary frame:
    -- a type Z with a point for every vertex, hence a type `PZ e` of paths
    -- spanning an edge.  It gets used twice, for the complex and for the
    -- collapsed complex.
    module Frame (Z : Type ℓ) (pt : V → Z) where
      PZ : Edges → Type ℓ
      PZ (u , v , e) = pt u ≡ pt v

      -- a square in Z spanning the four sides of s
      Sq□ : (s : Squares) → ((i : Side) → PZ (∂ s i)) → Type ℓ
      Sq□ (a , b , c , d , t , bo , l , r , σ) q = Square (q tp) (q bt) (q lf) (q rt)

      -- the boundary of s reassembled from all its sides but the k-th, and the
      -- k-th.  (A `Side` is not a record, so this has to be spelled out; it is
      -- what lets everything below avoid case splitting on `μ₁ s`.)
      ext : (s : Squares) (k : Side) → ((i : Side) → ¬ (i ≡ k) → PZ (∂ s i))
        → PZ (∂ s k) → (i : Side) → PZ (∂ s i)
      ext s tp rec p tp = p
      ext s tp rec p bt = rec bt bt≢tp
      ext s tp rec p lf = rec lf lf≢tp
      ext s tp rec p rt = rec rt rt≢tp
      ext s bt rec p tp = rec tp tp≢bt
      ext s bt rec p bt = p
      ext s bt rec p lf = rec lf lf≢bt
      ext s bt rec p rt = rec rt rt≢bt
      ext s lf rec p tp = rec tp tp≢lf
      ext s lf rec p bt = rec bt bt≢lf
      ext s lf rec p lf = p
      ext s lf rec p rt = rec rt rt≢lf
      ext s rt rec p tp = rec tp tp≢rt
      ext s rt rec p bt = rec bt bt≢rt
      ext s rt rec p lf = rec lf lf≢rt
      ext s rt rec p rt = p

      -- taking a boundary apart and putting it back together changes nothing
      Sq□ext : (s : Squares) (k : Side) (q : (i : Side) → PZ (∂ s i))
        → Sq□ s q → Sq□ s (ext s k (λ i _ → q i) (q k))
      Sq□ext s tp q x = x
      Sq□ext s bt q x = x
      Sq□ext s lf q x = x
      Sq□ext s rt q x = x

      Sq□ext⁻ : (s : Squares) (k : Side) (q : (i : Side) → PZ (∂ s i))
        → Sq□ s (ext s k (λ i _ → q i) (q k)) → Sq□ s q
      Sq□ext⁻ s tp q x = x
      Sq□ext⁻ s bt q x = x
      Sq□ext⁻ s lf q x = x
      Sq□ext⁻ s rt q x = x

      -- Three sides of a square determine the fourth, and the filler: this is
      -- the elementary collapse, and the fact that it is a *contractibility*
      -- rather than mere existence is what makes it usable one dimension up.
      freeContr : (s : Squares) (k : Side) (rec : (i : Side) → ¬ (i ≡ k) → PZ (∂ s i))
        → isContr (Σ[ p ∈ PZ (∂ s k) ] Sq□ s (ext s k rec p))
      freeContr (a , b , c , d , t , bo , l , r , σ) tp rec = contrTop _ _ _
      freeContr (a , b , c , d , t , bo , l , r , σ) bt rec = contrBot _ _ _
      freeContr (a , b , c , d , t , bo , l , r , σ) lf rec = contrLeft _ _ _
      freeContr (a , b , c , d , t , bo , l , r , σ) rt rec = contrRight _ _ _

    module FX = Frame ∣ V , E⁻ , (λ _ _ _ _ → ⊥*) ∣ (λ u → ∣ u ∣₀)
    module FY = Frame ∣ V , E , Sq ∣ (λ u → ∣ u ∣₀)

    -- the realisation of an edge, and of a square, in the complex itself
    edge₁ : (e : Edges) → FY.PZ e
    edge₁ (u , v , f) = ∣ u ⇒ v ∋ f ∣₁

    sq□ : (s : Squares) → FY.Sq□ s (λ i → edge₁ (∂ s i))
    sq□ (a , b , c , d , t , bo , l , r , σ) = ∣ t , bo , l , r ∋ σ ∣₂

    -- the collapsed complex includes into the complex
    ι : ∣ V , E⁻ , (λ _ _ _ _ → ⊥*) ∣ → ∣ V , E , Sq ∣
    ι ∣ u ∣₀ = ∣ u ∣₀
    ι (∣ u ⇒ v ∋ (f , _) ∣₁ i) = ∣ u ⇒ v ∋ f ∣₁ i
    ι (∣ _ , _ , _ , _ ∋ lift () ∣₂ i j)

    --------------------------------------------------------------------------
    -- The collapsing map
    --
    -- Every square is cancelled against the edge `μ̂₁ s` matched with it: that
    -- edge is sent to the path that runs around the other three sides.  Since
    -- those may themselves cap squares, this is a recursion, and it is
    -- well-founded exactly by acyclicity in dimension one.
    --
    -- Splitting an edge into the cases "caps a square", "matched with its
    -- source", "Critical" needs to decide whether an edge is matched upwards,
    -- which — unlike in dimension zero — is a search over squares rather than a
    -- consequence of `V-discrete`.  That decision is the `isUp?` field of the
    -- matching datum.

    P : Edges → Type ℓ
    P = FX.PZ

    -- where the matched side of a square goes: around the other three
    goUp : (s : Squares) (k : Side) (rec : (i : Side) → ¬ (i ≡ k) → P (∂ s i)) → P (∂ s k)
    goUp s k rec = fst (fst (FX.freeContr s k rec))

    goUpFill : (s : Squares) (k : Side) (rec : (i : Side) → ¬ (i ≡ k) → P (∂ s i))
      → FX.Sq□ s (FX.ext s k rec (goUp s k rec))
    goUpFill s k rec = snd (fst (FX.freeContr s k rec))

    -- The three edges a gradient colstep may leave `∂ s k` by are precisely the
    -- sides of s other than the matched one, which is why `goUp` may be fed
    -- with the recursive calls.
    colstep : (x : Edges) → Dec (isUp x) → ((y : Edges) → y <₁ x → P y) → P x
    colstep (u , v , f) (no ¬up) rec = ∣ u ⇒ v ∋ (f , ¬up) ∣₁
    colstep x (yes (s , p)) rec =
      subst P p (goUp s (μ₁ s) (λ i ne → rec (∂ s i) (s , p , i , ne , refl)))

    Φ : (e : Edges) → P e
    Φ = WFI.induction wf₁ (λ x rec → colstep x (isUp? x) rec)

    Φ-compute : (x : Edges) → Φ x ≡ colstep x (isUp? x) (λ y _ → Φ y)
    Φ-compute = WFI.induction-compute wf₁ (λ x rec → colstep x (isUp? x) rec)

    -- The recursion is only propositionally defined by its two cases, since
    -- the accessibility witness it recurses on does not compute.
    Φ-dn : (u v : V) (f : E u v) (¬up : ¬ isUp (u , v , f))
      → Φ (u , v , f) ≡ ∣ u ⇒ v ∋ (f , ¬up) ∣₁
    Φ-dn u v f ¬up = Φ-compute (u , v , f)
      ∙ cong (λ D → colstep (u , v , f) D (λ y _ → Φ y))
              (isPropDec (isUp-isHProp (u , v , f)) (isUp? (u , v , f)) (no ¬up))

    Φ-up : (s : Squares) → Φ (μ̂₁ s) ≡ goUp s (μ₁ s) (λ i _ → Φ (∂ s i))
    Φ-up s = Φ-compute (μ̂₁ s)
      ∙ cong (λ D → colstep (μ̂₁ s) D (λ y _ → Φ y))
              (isPropDec (isUp-isHProp (μ̂₁ s)) (isUp? (μ̂₁ s)) (yes (s , refl)))
      ∙ substRefl {B = P} {x = μ̂₁ s} (goUp s (μ₁ s) (λ i _ → Φ (∂ s i)))

    -- hence every square becomes degenerate: it is filled by the very square
    -- that `goUp` produced along with the matched side.
    ϕ□ : (s : Squares) → FX.Sq□ s (λ i → Φ (∂ s i))
    ϕ□ s = FX.Sq□ext⁻ s (μ₁ s) (λ i → Φ (∂ s i))
      (subst (λ p → FX.Sq□ s (FX.ext s (μ₁ s) (λ i _ → Φ (∂ s i)) p))
              (sym (Φ-up s)) (goUpFill s (μ₁ s) (λ i _ → Φ (∂ s i))))

    ϕ : ∣ V , E , Sq ∣ → ∣ V , E⁻ , (λ _ _ _ _ → ⊥*) ∣
    ϕ ∣ u ∣₀ = ∣ u ∣₀
    ϕ (∣ u ⇒ v ∋ f ∣₁ i) = Φ (u , v , f) i
    ϕ (∣_,_,_,_∋_∣₂ {a} {b} {c} {d} t bo l r σ i j) =
      ϕ□ (a , b , c , d , t , bo , l , r , σ) i j

    --------------------------------------------------------------------
    -- ϕ is inverse to the inclusion
    --
    -- One direction is immediate: ϕ leaves an edge capping no square alone.

    sec : (x : ∣ V , E⁻ , (λ _ _ _ _ → ⊥*) ∣) → ϕ (ι x) ≡ x
    sec ∣ u ∣₀ = refl
    sec (∣ u ⇒ v ∋ (f , ¬up) ∣₁ j) = λ κ → Φ-dn u v f ¬up κ j
    sec (∣ _ , _ , _ , _ ∋ lift () ∣₂ i j)

    -- The other direction is again a recursion on the gradient order: the
    -- path around a square has to be pushed back across the square.  Its
    -- value on the matched side is *not* chosen — it is read off, together
    -- with the cube that the square case of the homotopy needs, from the
    -- contractibility of "fourth side plus filler".  That is what keeps the
    -- coherence in dimension two for free.

    Q : Edges → Type ℓ
    Q e = Path (FY.PZ e) (cong ι (Φ e)) (edge₁ e)

    ιϕ□ : (s : Squares) → FY.Sq□ s (λ i → cong ι (Φ (∂ s i)))
    ιϕ□ (a , b , c , d , t , bo , l , r , σ) i j =
      ι (ϕ□ (a , b , c , d , t , bo , l , r , σ) i j)

    -- a path in the contractible type of "k-th side plus filler", from the
    -- collapsed square to the square itself
    WT : (s : Squares) (k : Side) → ((i : Side) → ¬ (i ≡ k) → Q (∂ s i)) → Type ℓ
    WT s k rec =
      PathP (λ κ → Σ[ p ∈ FY.PZ (∂ s k) ] FY.Sq□ s (FY.ext s k (λ i ne → rec i ne κ) p))
        (cong ι (Φ (∂ s k)) , FY.Sq□ext s k (λ i → cong ι (Φ (∂ s i))) (ιϕ□ s))
        (edge₁ (∂ s k) , FY.Sq□ext s k (λ i → edge₁ (∂ s i)) (sq□ s))

    W : (s : Squares) (k : Side) (rec : (i : Side) → ¬ (i ≡ k) → Q (∂ s i)) → WT s k rec
    W s k rec = isOfHLevelPathP' 0
      (isContr→isProp (FY.freeContr s k (λ i ne → rec i ne i1))) _ _ .fst

    Λgo : (s : Squares) (k : Side) (rec : (i : Side) → ¬ (i ≡ k) → Q (∂ s i)) → Q (∂ s k)
    Λgo s k rec κ = fst (W s k rec κ)

    Λcolstep : (x : Edges) → Dec (isUp x) → ((y : Edges) → y <₁ x → Q y) → Q x
    Λcolstep (u , v , f) (no ¬up) rec = cong (cong ι) (Φ-dn u v f ¬up)
    Λcolstep x (yes (s , p)) rec =
      subst Q p (Λgo s (μ₁ s) (λ i ne → rec (∂ s i) (s , p , i , ne , refl)))

    Λ : (e : Edges) → Q e
    Λ = WFI.induction wf₁ (λ x rec → Λcolstep x (isUp? x) rec)

    Λ-compute : (x : Edges) → Λ x ≡ Λcolstep x (isUp? x) (λ y _ → Λ y)
    Λ-compute = WFI.induction-compute wf₁ (λ x rec → Λcolstep x (isUp? x) rec)

    Λ-up : (s : Squares) → Λ (μ̂₁ s) ≡ Λgo s (μ₁ s) (λ i _ → Λ (∂ s i))
    Λ-up s = Λ-compute (μ̂₁ s)
      ∙ cong (λ D → Λcolstep (μ̂₁ s) D (λ y _ → Λ y))
              (isPropDec (isUp-isHProp (μ̂₁ s)) (isUp? (μ̂₁ s)) (yes (s , refl)))
      ∙ substRefl {B = Q} {x = μ̂₁ s} (Λgo s (μ₁ s) (λ i _ → Λ (∂ s i)))

    Λ-up' : (s : Squares) (k : Side) (eq : μ₁ s ≡ k)
      → Λ (∂ s k) ≡ Λgo s k (λ i _ → Λ (∂ s i))
    Λ-up' s k eq =
      transport (λ κ → Λ (∂ s (eq κ)) ≡ Λgo s (eq κ) (λ i _ → Λ (∂ s i))) (Λ-up s)

    -- the cube the square case of the homotopy asks for
    C : (s : Squares) → PathP (λ κ → FY.Sq□ s (λ i → Λ (∂ s i) κ)) (ιϕ□ s) (sq□ s)
    C s = Caux s (μ₁ s) refl where
      -- This is the one place where the matched side has to be named: the four
      -- clauses are the same text, but `ext` only computes on a concrete side,
      -- and here the cube's two ends are the square before and after
      -- collapsing, with no `ext` left to take them apart.
      Caux : (s : Squares) (k : Side) → μ₁ s ≡ k → PathP (λ κ → FY.Sq□ s (λ i → Λ (∂ s i) κ)) (ιϕ□ s) (sq□ s)
      Caux s tp eq = subst
        (λ z → PathP (λ κ → FY.Sq□ s (FY.ext s tp (λ i _ → Λ (∂ s i) κ) (z κ))) (ιϕ□ s) (sq□ s))
        (sym (Λ-up' s tp eq)) (λ κ → snd (W s tp (λ i _ → Λ (∂ s i)) κ))
      Caux s bt eq = subst
        (λ z → PathP (λ κ → FY.Sq□ s (FY.ext s bt (λ i _ → Λ (∂ s i) κ) (z κ))) (ιϕ□ s) (sq□ s))
        (sym (Λ-up' s bt eq)) (λ κ → snd (W s bt (λ i _ → Λ (∂ s i)) κ))
      Caux s lf eq = subst
        (λ z → PathP (λ κ → FY.Sq□ s (FY.ext s lf (λ i _ → Λ (∂ s i) κ) (z κ))) (ιϕ□ s) (sq□ s))
        (sym (Λ-up' s lf eq)) (λ κ → snd (W s lf (λ i _ → Λ (∂ s i)) κ))
      Caux s rt eq = subst
        (λ z → PathP (λ κ → FY.Sq□ s (FY.ext s rt (λ i _ → Λ (∂ s i) κ) (z κ))) (ιϕ□ s) (sq□ s))
        (sym (Λ-up' s rt eq)) (λ κ → snd (W s rt (λ i _ → Λ (∂ s i)) κ))


    ret : (y : ∣ V , E , Sq ∣) → ι (ϕ y) ≡ y
    ret ∣ u ∣₀ = refl
    ret (∣ u ⇒ v ∋ f ∣₁ j) = λ κ → Λ (u , v , f) κ j
    ret (∣_,_,_,_∋_∣₂ {a} {b} {c} {d} t bo l r σ i j) =
      λ κ → C (a , b , c , d , t , bo , l , r , σ) κ i j



--------------------------------------------------------------------------
-- The theorem
--
-- The realisation of the complex is the realisation of the complex
-- collapsed along the matching: cancel the squares against the faces `μ₁`
-- picks for them, read what is left as a graph, and cancel the vertices
-- against the edges `μ` picks for them.


module Morse {V : Type ℓ} {E : V → V → Type ℓ} {Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type ℓ}
  (K : Complex V E Sq) (M : 2FullMatching K) where

  open MorseSquares K M public
  MorseTheorem : ∣ V , E , Sq ∣ ≡ GR.∣ Crit₀ , P⁻.Crit₁ ∣
  MorseTheorem = SquareCollapse ∙ noSq ∙ Mo⁻.MorseTheorem
