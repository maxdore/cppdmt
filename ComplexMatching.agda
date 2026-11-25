{-# OPTIONS --cubical --guardedness --safe #-}
module ComplexMatching where

open import Cubical.Foundations.Prelude
  renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded

open import Prelude
import GraphMatching as GM
open GM using (Graph)

private
  variable
    ℓ : Level

module Cells (V : Type ℓ) (E : V → V → Type ℓ)
    (Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type ℓ) where

  -- the 1-cells are from the development of Graphs
  open GM.Edge E public

  -- bundled 2-cells
  SquareOn : (a b c d : V) → Type ℓ
  SquareOn a b c d =
    Σ[ t ∈ E a b ] Σ[ bo ∈ E c d ] Σ[ l ∈ E a c ] Σ[ r ∈ E b d ] Sq t bo l r

  Squares : Type ℓ
  Squares = Σ[ a ∈ V ] Σ[ b ∈ V ] Σ[ c ∈ V ] Σ[ d ∈ V ] SquareOn a b c d

  -- the boundary function, to ensure distinct faces for a square
  ∂ : Squares → Side → Edges
  ∂ (a , b , c , d , t , bo , l , r , _) tp = a , b , t
  ∂ (a , b , c , d , t , bo , l , r , _) bt = c , d , bo
  ∂ (a , b , c , d , t , bo , l , r , _) lf = a , c , l
  ∂ (a , b , c , d , t , bo , l , r , _) rt = b , d , r

record Complex (V : Type ℓ) (E : V → V → Type ℓ)
    (Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type ℓ)
    : Type ℓ where
  open Cells V E Sq public

  field
    graph : Graph V E

    Sq-isHProp : {a b c d : V} (t : E a b) (bo : E c d) (l : E a c) (r : E b d)
      → isHProp (Sq t bo l r)

    -- non-degeneracy: the four boundary edges of a square are pairwise distinct
    ∂-inj : (s : Squares) {i j : Side} → ∂ s i ≡ ∂ s j → i ≡ j

  open Graph graph public

  SquareOn-isHProp : (a b c d : V) → isHProp (SquareOn a b c d)
  SquareOn-isHProp a b c d =
    isPropΣ (E-isHProp _ _) λ t → isPropΣ (E-isHProp _ _) λ bo →
    isPropΣ (E-isHProp _ _) λ l → isPropΣ (E-isHProp _ _) λ r → Sq-isHProp t bo l r


  Squares-discrete : Discrete Squares
  Squares-discrete (a , b , c , d , s) (a' , b' , c' , d' , s')
    with V-discrete a a' | V-discrete b b' | V-discrete c c' | V-discrete d d'
  ... | no ¬p | _      | _      | _      = no λ r → ¬p (cong fst r)
  ... | yes p | no ¬q  | _      | _      = no λ r → ¬q (cong (fst ∘ snd) r)
  ... | yes p | yes q  | no ¬o  | _      = no λ r → ¬o (cong (fst ∘ snd ∘ snd) r)
  ... | yes p | yes q  | yes o  | no ¬n  = no λ r → ¬n (cong (fst ∘ snd ∘ snd ∘ snd) r)
  ... | yes p | yes q  | yes o  | yes n  = yes (ΣPathP (p , ΣPathP (q , ΣPathP (o , ΣPathP (n ,
        isProp→PathP (λ i → SquareOn-isHProp (p i) (q i) (o i) (n i)) s s')))))

  Squares-isHSet : isHSet Squares
  Squares-isHSet = Discrete→isSet Squares-discrete


-- Matchings

module _ {V : Type ℓ} {E : V → V → Type ℓ}
    {Sq : {a b c d : V} → E a b → E c d → E a c → E b d → Type ℓ}
    (K : Complex V E Sq) where

  open Complex K

  record MatchingData : Type ℓ where
    field
      μ₀ : V → V
      μ₁ : Squares → Side

    -- the edge a square is matched with
    μ̂₁ : Squares → Edges
    μ̂₁ s = ∂ s (μ₁ s)

    isUp : Edges → Type ℓ
    isUp e = Σ[ s ∈ Squares ] μ̂₁ s ≡ e

    isDn : Edges → Type ℓ
    isDn e = let (u , v , _) = e in μ₀ u ≡ v

    field
      μ̂₁-inj : {s s' : Squares} → μ̂₁ s ≡ μ̂₁ s' → s ≡ s'
      up∩dn : (e : Edges) → isUp e → ¬ isDn e
      isUp? : (e : Edges) → Dec (isUp e)

  -- Gradient-path machinery over a fixed matching datum.
  module GradientPaths (m : MatchingData) where
    open MatchingData m public

    -- dimension 0 is inherited from graphs
    open GM.Paths graph μ₀ public

    isUp-isHProp : (e : Edges) → isHProp (isUp e)
    isUp-isHProp e (s , p) (s' , q) =
      Σ≡Prop (λ _ → Edges-isHSet _ _) (μ̂₁-inj (p ∙ sym q))

    isDn-isHProp : (e : Edges) → isHProp (isDn e)
    isDn-isHProp e = V-isHSet _ _

    -- Critical cells

    isCrit₁ : Edges → Type ℓ
    isCrit₁ e = (¬ isDn e) × (¬ isUp e)

    isCrit₁-isHProp : (e : Edges) → isHProp (isCrit₁ e)
    isCrit₁-isHProp e = isProp× (isProp¬ _) (isProp¬ _)

    Crits₁ : Type ℓ
    Crits₁ = Σ[ e ∈ Edges ] isCrit₁ e

    Crits₁-isHSet : isHSet Crits₁
    Crits₁-isHSet = isSetΣSndProp Edges-isHSet isCrit₁-isHProp

    -- gradient steps and paths in dimension one
    _⇒₁_ : Edges → Edges → Type ℓ
    e ⇒₁ f = Σ[ s ∈ Squares ] (μ̂₁ s ≡ e) × (Σ[ i ∈ Side ] (¬ i ≡ μ₁ s) × (∂ s i ≡ f)) -- exitData s f

    upStep : {e f : Edges} → e ⇒₁ f → isUp e
    upStep (s , p , _) = s , p

    -- paths terminate at edges that are not matched upwards 
    data _⇝₁_ : Edges → Edges → Type ℓ where
      end : {e f : Edges} → ¬ isUp e → e ≡ f → e ⇝₁ f
      step  : ∀ {e} (f) {g} → e ⇒₁ f → f ⇝₁ g → e ⇝₁ g

    -- acyclicity in dimension one
    _<₁_ : Edges → Edges → Type ℓ
    f <₁ e = e ⇒₁ f

    acyclic₁ : Type ℓ
    acyclic₁ = WellFounded _<₁_

  2FullMatching : Type ℓ
  2FullMatching = Σ[ m ∈ MatchingData ]
      GradientPaths.acyclic m × WellFounded (GradientPaths._<₁_ m)

