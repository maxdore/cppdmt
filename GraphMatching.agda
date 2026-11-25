{-# OPTIONS --cubical --guardedness --safe  #-}
module GraphMatching where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Relation.Nullary

open import Prelude

private
  variable
    ℓ : Level

module Edge {V : Type ℓ} (E : V → V → Type ℓ) where
  Edges : Type ℓ
  Edges = Σ[ u ∈ V ] Σ[ v ∈ V ] E u v

  src tgt : Edges → V
  src (u , _ , _) = u
  tgt (_ , v , _) = v

record Graph (V : Type ℓ) (E : V → V → Type ℓ) : Type ℓ where
  field
    V-discrete : Discrete V
    E-isIrrefl : (u : V) → ¬ (E u u)
    E-isHProp : (u v : V) → isHProp (E u v)

  -- Use Hedberg's theorem to show V is a set
  V-isHSet : isHSet V
  V-isHSet = Discrete→isSet V-discrete

  open Edge E

  Edges-discrete : Discrete Edges
  Edges-discrete (u , v , x) (u' , v' , x') with V-discrete u u' | V-discrete v v'
  ... | no ¬p | _      = no λ r → ¬p (cong fst r)
  ... | yes p | no ¬q  = no λ r → ¬q (cong (fst ∘ snd) r)
  ... | yes p | yes q  = yes (ΣPathP (p , ΣPathP (q ,
            isProp→PathP (λ i → E-isHProp (p i) (q i)) x x')))

  Edges-isHSet : isHSet Edges
  Edges-isHSet = Discrete→isSet Edges-discrete

module Paths {V : Type ℓ} {E : V → V → Type ℓ} (G : Graph V E) (μ : V → V) where
  open Graph G
  open Edge E

  isCrit₀ : V → Type ℓ
  isCrit₀ u = μ u ≡ u

  Crit₀ : Type ℓ
  Crit₀ = Σ[ u ∈ V ] isCrit₀ u

  _ᵥ : Crit₀ → V
  _ᵥ = fst
  infix 100 _ᵥ

  isCritIsHProp : (u : V) → isHProp (isCrit₀ u)
  isCritIsHProp u = V-isHSet _ _

  Crit₀IsHSet : isHSet Crit₀
  Crit₀IsHSet = isSetΣSndProp V-isHSet isCritIsHProp

  _⇒ᵐ_ _⇒ᶜ_ : (u v : V) → Type ℓ
  u ⇒ᵐ v = μ u ≡ v -- E u v × (μ u ≡ v)
  u ⇒ᶜ v = μ u ≢ v -- E u v × (μ u ≢ v)

  ⇒ᵐIsHProp : {u v : V} → isHProp (u ⇒ᵐ v)
  ⇒ᵐIsHProp = V-isHSet _ _ -- isProp× (E-isHProp _ _) (V-isHSet _ _)

  ⇒ᶜIsHProp : {u v : V} → isHProp (u ⇒ᶜ v)
  ⇒ᶜIsHProp = λ p q i x → absurd {A = Path ⊥ (p x) (q x)} (p x) i -- isProp× (E-isHProp _ _) λ p q i x → absurd {A = Path ⊥ (p x) (q x)} (p x) i

  data _⇝_ : (u v : V) → Type ℓ where
    end : {u v : V} → isCrit₀ u → u ≡ v → u ⇝ v
    step : ∀{(u , v , e) : Edges} {w} → (u ⇒ᵐ v) → (v ⇝ w) → (u ⇝ w)

  Crit₁ : Crit₀ → Crit₀ → Type ℓ
  Crit₁ c d = Σ[ (u , v , e) ∈ Edges ] ((u ⇒ᶜ v) × (u ⇝ c ᵥ) × (v ⇝ d ᵥ))

  acyclic : Type ℓ
  acyclic = (u : V) → Σ[ c ∈ Crit₀ ] u ⇝ c ᵥ



module _ {V : Type ℓ} {E : V → V → Type ℓ} where
  Matching : (G : Graph V E) → Type ℓ
  Matching G = Σ[ μ ∈ (V → V) ] acyclic G μ
    where open Paths


module Matching {V : Type ℓ} {E : V → V → Type ℓ} (G : Graph V E) ((μ , μ-acy) : Matching G) where
  open Graph G
  open Paths G μ public

  _Crit? : (u : V) → Dec (isCrit₀ u)
  u Crit? = V-discrete (μ u) u

  _⇒ᵐ?_ : (u v : V) → Dec (μ u ≡ v)
  u ⇒ᵐ? v = V-discrete (μ u) v

  _⇒ᶜ?_ : (u v : V) → Dec (u ⇒ᶜ v)
  u ⇒ᶜ? v = Dec¬ (u ⇒ᵐ? v)

  sink : V → Crit₀
  sink u = fst (μ-acy u)
  _⇝sink : (u : V) → u ⇝ (sink u)ᵥ
  u ⇝sink = snd (μ-acy u)

  sinkUniq : {u : V} (c d : V) → (u ⇝ c) → (u ⇝ d) → c ≡ d
  sinkUniq c d (end μ a) (end μ' b) = sym a ∙ b
  sinkUniq c d (step {_ , v , e} μ p) (step {_ , v' , e'} μ' q) =
    sinkUniq c d p (subst (_⇝ d) (sym μ' ∙ μ) q)
  sinkUniq {u} c d (end μ a) (step {_ , v , e} μ' p) =
    absurd (E-isIrrefl u (subst (E u) (sym μ' ∙ μ) e))
  sinkUniq {u} c d (step {_ , v , e} μ p) (end μ' a) =
    absurd (E-isIrrefl u (subst (E u) (sym μ ∙ μ') e))

  sinkUniqᶜ : {u : V} → (c d : Crit₀) → u ⇝ (fst c) → u ⇝ (fst d)
    → c ≡ d
  sinkUniqᶜ c d p q = Σ≡Prop isCritIsHProp (sinkUniq (fst c) (fst d) p q)


  σ : (u : V) (c : Crit₀) (p : u ⇝ c ᵥ) → sink u ≡ c
  σ u c p = sinkUniqᶜ (sink u) c (u ⇝sink) p


  ⇝IsHProp : {u : V} → (c : Crit₀) → isHProp (u ⇝ c ᵥ)
  ⇝IsHProp {u} c (end μ a) (end μ' b) i =
    end (isCritIsHProp u μ μ' i) (V-isHSet u (c ᵥ) a b i)
  ⇝IsHProp {u} c (step {_ , v , e} μ p) (step {_ , v' , e'} μ' q) i =
    step {u , v≡v' i , e≡e' i} (μ≡μ' i) (IH' i)
    where
    v≡v' = sym μ ∙ μ'

    -- the edge witness now travels inside `step`, so it has to be transported
    -- along `v≡v'` too; `E-isHProp` makes that transport contractible
    e≡e' : PathP (λ i → E u (v≡v' i)) e e'
    e≡e' = isProp→PathP (λ i → E-isHProp u (v≡v' i)) e e'

    IH : Path (v' ⇝ fst c) (subst (_⇝ fst c) v≡v' p) q
    IH = ⇝IsHProp {v'} c (subst (_⇝ fst c) v≡v' p) q

    IH' : PathP (λ i → v≡v' i ⇝ fst c) p q
    IH' = toPathP (fromPathP (subst-filler (_⇝ fst c) v≡v' p)
                    ∙ sym (fromPathP {A = λ i → v' ⇝ fst c} (symP IH))
                    ∙ λ i → transp (λ _ → v' ⇝ fst c) i q)

    μ≡μ' : PathP (λ i → _⇒ᵐ_ u (v≡v' i)) μ μ'
    μ≡μ' = toPathP (fromPathP (subst-filler (u ⇒ᵐ_) v≡v' μ)
                    ∙ (⇒ᵐIsHProp (subst (u ⇒ᵐ_) v≡v' μ) μ'))

  ⇝IsHProp {u} c (end μ a) (step {_ , v , e} μ' q) =
    absurd (E-isIrrefl u (subst (E u) (sym μ' ∙ μ) e))
  ⇝IsHProp {u} c (step {_ , v , e} μ p) (end μ' b) =
    absurd (E-isIrrefl u (subst (E u) (sym μ ∙ μ') e))

  ⇝IsHPropS : {u : V} → (c d : Crit₀) → (p : u ⇝ (fst c)) → (q : u ⇝ (fst d))
    → PathP (λ i → u ⇝ (sinkUniq (fst c) (fst d) p q i)) p q
  ⇝IsHPropS {u} c d p q = toPathP
    (fromPathP (subst-filler (u ⇝_) (sinkUniq (c ᵥ) (d ᵥ) p q) p)
    ∙ ⇝IsHProp d (subst (u ⇝_) (sinkUniq (c ᵥ) (d ᵥ) p q) p) q)

  Crit₁IsHSet : (c d : Crit₀) → isHSet (Crit₁ c d)
  Crit₁IsHSet c d = isSetΣSndProp Edges-isHSet λ (u , v , e) →
    isProp× ⇒ᶜIsHProp (isProp× (⇝IsHProp c) (⇝IsHProp d))



  comp⇝ : (u v : V) (c : Crit₀) → (u ⇝ c ᵥ) → Dec (u ⇝ v)
  comp⇝ u v c (end a b) with V-discrete v (c ᵥ)
  ... | yes p = yes (end a (b ∙ sym p))
  ... | no ¬p = no λ q → absurd (¬p (sinkUniq v (c ᵥ) q (end a b)))

  comp⇝ u v c (step {_ , w , e} x p) with comp⇝ w v c p
  ... | yes q = yes (step {u , w , e} x q)
  ... | no ¬q = no λ r →
    absurd (¬q (subst (w ⇝_) (sym (sinkUniq v (c ᵥ) r (step {u , w , e} x p))) p))

  _⇝?_ : (u v : V) → Dec (u ⇝ v)
  u ⇝? v = comp⇝ u v (sink u) (u ⇝sink)

  module compE (E? : ((u v : V) → Dec (E u v))) where
    -- the data an edge carries in `Crit₁`
    path? : (c d : V) (u v : V) → Dec (u ⇒ᶜ v × u ⇝ c × v ⇝ d)
    path? c d u v = Dec× (u ⇒ᶜ? v) (Dec× (u ⇝? c) (v ⇝? d))


