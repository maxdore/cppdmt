{-# OPTIONS --cubical --guardedness --safe #-}

-- Two vertices with an edge each way:
--
--     true ⇄ false
--
-- One of the two edges is a spanning tree and the other closes a cycle, so this
-- is `GraphBouquet` with a single leftover edge and not the Morse theorem:
-- there is nothing to match away first.
--
-- `CycleCollapse` asks for the edges already split as `T u v ⊎ L u v`, whereas
-- `two₁` names the edge relation directly, so the collapse is preceded by
-- `isoReal` relabelling `two₁` as `tree₁ ⊎ loop₁` — the same shuffling of
-- constructors that `Examples.Bouquets` does at the far end of each chain, to
-- read the one-element `Loops` as `⊤₁` and hence the bouquet as `S¹`.
module Examples.Two where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Relation.Nullary
open import Cubical.HITs.S1
open import Cubical.Algebra.Group.Morphisms
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Sn
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.Unit

open import Prelude
open import GraphMatching
open import CType1
import GraphBouquet as GB

two₁ : Bool → Bool → Type
two₁ false false = ⊥
two₁ false true = ⊤
two₁ true false = ⊤
two₁ true true = ⊥

two : Graph Bool two₁
Graph.V-discrete two = _≟_
Graph.E-isIrrefl two false ()
Graph.E-isIrrefl two true ()
Graph.E-isHProp two false true = isHProp⊤
Graph.E-isHProp two true false = isHProp⊤

two₁? : (u v : Bool) → Dec (two₁ u v)
two₁? false false = no (λ a → a)
two₁? false true = yes tt
two₁? true false = yes tt
two₁? true true = no (λ a → a)


--------------------------------------------------------------------------------
-- The same graph with its edges split
--
-- The spanning tree is the edge from `true` to `false`; the edge back from
-- `false` to `true` is the one left over, and becomes the circle.

tree₁ : Bool → Bool → Type
tree₁ false false = ⊥
tree₁ false true = ⊥
tree₁ true false = ⊤
tree₁ true true = ⊥

loop₁ : Bool → Bool → Type
loop₁ false false = ⊥
loop₁ false true = ⊤
loop₁ true false = ⊥
loop₁ true true = ⊥

two₁≡⊎ : ∣ Bool , two₁ ∣ ≡ ∣ Bool , (λ u v → tree₁ u v ⊎ loop₁ u v) ∣
two₁≡⊎ = isoReal (λ b → b) F₁ (λ b → b) G₁ (λ _ → refl) S₁ (λ _ → refl) R₁
  where
  F₁ : (x y : Bool) → two₁ x y → tree₁ x y ⊎ loop₁ x y
  F₁ false false ()
  F₁ false true tt = inr tt
  F₁ true false tt = inl tt
  F₁ true true ()
  G₁ : (x y : Bool) → tree₁ x y ⊎ loop₁ x y → two₁ x y
  G₁ false false (inl ())
  G₁ false true (inl ())
  G₁ false true (inr tt) = tt
  G₁ true false (inl tt) = tt
  G₁ true true (inr ())
  S₁ : (x y : Bool) (f : tree₁ x y ⊎ loop₁ x y)
    → PathP (λ i → tree₁ x y ⊎ loop₁ x y) (F₁ x y (G₁ x y f)) f
  S₁ false false (inl ())
  S₁ false true (inl ())
  S₁ false true (inr tt) = refl
  S₁ true false (inl tt) = refl
  S₁ true true (inr ())
  R₁ : (x y : Bool) (f : two₁ x y) → PathP (λ i → two₁ x y) (G₁ x y (F₁ x y f)) f
  R₁ false true tt = refl
  R₁ true false tt = refl

-- the tree is one edge, so the path from the root is that edge …
P : (v : Bool) → Path (∣ Bool , tree₁ ∣) (∣ true ∣₀) (∣ v ∣₀)
P false = refl ∙ ∣ true ⇒ false ∋ tt ∣₁
P true = refl

-- … and its triangle is the filler of that composition
Fill : {u v : Bool} (t : tree₁ u v)
  → PathP (λ i → Path (∣ Bool , tree₁ ∣) (∣ true ∣₀) (∣ u ⇒ v ∋ t ∣₁ i)) (P u) (P v)
Fill {false} {false} ()
Fill {false} {true} ()
Fill {true} {false} tt = compPath-filler refl ∣ true ⇒ false ∋ tt ∣₁
Fill {true} {true} ()

-- one edge outside the tree, so one circle
∣two₁∣≡S¹ : ∣ Bool , two₁ ∣ ≡ S¹
∣two₁∣≡S¹ = two₁≡⊎
  ∙ GB.CycleCollapse tree₁ loop₁ true P Fill
  ∙ sym ∣pt∣≡Bouquet
  ∙ isoReal (λ _ → tt)  (λ _ _ _ → tt)
            (λ _ → tt*) (λ _ _ _ → false , true , tt)
            (λ _ → refl) (λ _ _ _ → refl)
            (λ _ → refl) (λ { _ _ (false , true , tt) → refl
                            ; _ _ (true , false , ()) ; _ _ (true , true , ()) })
  ∙ sym S¹≡∣⊤₁∣


∣two₁∣-Groupoid : isGroupoid ∣ Bool , two₁ ∣
∣two₁∣-Groupoid = subst isGroupoid (sym ∣two₁∣≡S¹) isGroupoidS¹


H¹-two≅ℤ : GroupIso (coHomGr 1 (∣ Bool , two₁ ∣)) ℤGroup
H¹-two≅ℤ = subst (λ A → GroupIso (coHomGr 1 A) ℤGroup) (sym ∣two₁∣≡S¹) H¹-S¹≅ℤ

Hⁿ⁺²-two≅0 : (n : ℕ) → coHomGr (2 + n) ∣ Bool , two₁ ∣ ≅ ⊤Group
Hⁿ⁺²-two≅0 n = subst (λ A → GroupIso (coHomGr (2 + n) A) ⊤Group)
  (sym ∣two₁∣≡S¹) (Hⁿ-S¹≅0 n)
