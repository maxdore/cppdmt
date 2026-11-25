{-# OPTIONS --cubical --guardedness --safe #-}
module GraphMorse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels renaming (isSet→SquareP to isHSet→SquareP)
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary

open import Prelude
open import CType1
open import GraphMatching

private
  variable
    ℓ : Level

module Morse {V : Type ℓ} {E : V → V → Type ℓ}  (G : Graph V E) ((M , wf) : Matching G) where
  open Graph G
  open Matching G (M , wf) public

  ∣_∣⇝ : {u v : V} → u ⇝ v → ∣ u ∣₀ ≡ ∣ v ∣₀
  ∣ end μ a ∣⇝ = cong ∣_∣₀ a
  ∣_∣⇝ {u} (step {_ , v , e} μ p) = ∣ u ⇒ v ∋ e ∣₁ ∙ ∣ p ∣⇝

  ι : ∣ Crit₀ , Crit₁ ∣ → ∣ V , E ∣
  ι (∣ c ∣₀) = ∣ c ᵥ ∣₀
  ι (∣ c ⇒ d ∋ ((u , v , e) , ¬μ , p , q) ∣₁ i) =
    ((sym ∣ p ∣⇝) ∙∙ (∣ u ⇒ v ∋ e ∣₁) ∙∙ ∣ q ∣⇝) i

  ϕ : ∣ V , E ∣ → ∣ Crit₀ , Crit₁ ∣
  ϕ (∣ u ∣₀) = ∣ sink u ∣₀
  ϕ (∣ u ⇒ v ∋ f ∣₁ i) with u ⇒ᵐ? v
  ... | yes μ = ∣ σ u (sink v) (step {u , v , f} μ (v ⇝sink)) i ∣₀
  ... | no ¬μ = ∣ sink u ⇒ sink v ∋ ((u , v , f) , ¬μ , (u ⇝sink) , (v ⇝sink)) ∣₁ i

  ⇝Contr : (u : V) (c : Crit₀) (p : u ⇝ c ᵥ) →
   PathP (λ i → Path (∣ Crit₀ , Crit₁ ∣)
      ∣ σ u c p i ∣₀
      ∣ σ (c ᵥ) c (end (snd c) refl) i ∣₀)
      (λ j → ϕ (∣ p ∣⇝ j))
      (λ j → ∣ c ∣₀)

  ⇝Contr u c (end μ a) = λ i j →
    ∣ isHSet→SquareP (λ _ _ → Crit₀IsHSet)
      (σ u c (end μ a))
      (σ (c ᵥ) c (end (snd c) refl))
      (cong sink a)
      (λ _ → c) j i ∣₀

  ⇝Contr u c (step {_ , v , f} μ p)
    with u ⇒ᵐ? v
  ...| no ¬μ = absurd (¬μ μ)
  ...| yes μ'
    = λ i j → hcomp (λ k → λ {
      (i = i0) → compFiller k j
    ; (i = i1) → ∣ c ∣₀
    ; (j = i0) → ∣ σ u c (step {u , v , f} μ p) i ∣₀
    ; (j = i1) → ⇝Contr v c p i k
    }) (∣ isHSet→SquareP (λ _ _ → Crit₀IsHSet)
            (σ u (sink v) (step {u , v , f} μ (v ⇝sink)))
            (λ _ → c)
            (σ u c (step {u , v , f} μ p))
            (σ v c p) i j ∣₀)
      where
      transportFiller : PathP (λ i → Path (∣ Crit₀ , Crit₁ ∣) (∣ sink u ∣₀) (∣ sink (fst c) ∣₀))
        (λ j → (hcomp (λ k → λ {
          (j = i0) → ϕ (∣ u ∣₀)
        ; (j = i1) → ϕ (∣ p ∣⇝ k)
        }) ∣ σ u (sink v) (step {u , v , f} μ (v ⇝sink)) j ∣₀))
        (λ j → hcomp (λ k →
            λ { (j = i0) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣ u ∣₀))
              ; (j = i1) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣ p ∣⇝ k))
              }) ∣ transp (λ i → Crit₀) i0 (σ u (sink v) (step {u , v , f} μ' (v ⇝sink)) j) ∣₀ )
      transportFiller i j = hcomp (λ k →
            λ { (j = i0) → ∣ transportRefl (sink u) (~ i ∨ k) ∣₀
              ; (j = i1) → transportRefl (ϕ (∣ p ∣⇝ k)) (~ i ∨ k)
              }) (hcomp (λ k →
              λ { (i = i0) → ∣ σ u (sink v) (step {u , v , f} (⇒ᵐIsHProp μ' μ k) (v ⇝sink)) j ∣₀
              ; (i = i1) → ∣ transportRefl (σ u (sink v) (step {u , v , f} μ' (v ⇝sink)) j) (~ k)  ∣₀
                ; (j = i0) → transportRefl (∣ sink u ∣₀) (~ i ∨ ~ k)
                ; (j = i1) → transportRefl (∣ sink v ∣₀) (~ i ∨ ~ k)
                }) ∣ σ u (sink v) (step {u , v , f} μ' (v ⇝sink)) j ∣₀)

      compFiller : PathP (λ i → ∣ sink u ∣₀ ≡ ϕ (∣ p ∣⇝ i))
        (λ i → ∣ σ u (sink v) (step {u , v , f} μ (v ⇝sink)) i ∣₀)
        λ j → hcomp (λ k → (λ {
                  (j = i0) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣ u ∣₀))
                ; (j = i1) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣ p ∣⇝ k))
                })) ∣ transp (λ i → Crit₀) i0 (σ u (sink v) (step {u , v , f} μ' (v ⇝sink)) j) ∣₀
      compFiller = toPathP
                  ((fromPathP (compPath-filler (λ i → ∣ σ u (sink v) (step {u , v , f} μ (v ⇝sink)) i ∣₀)
                                            (λ i → ϕ (∣_∣⇝ {u = v} {v = fst c} p i)))) ∙ transportFiller)


  rinv : (y : ∣ Crit₀ , Crit₁ ∣) → ϕ (ι y) ≡ y

  rinv (∣ c ∣₀) = cong ∣_∣₀ (σ (c ᵥ) c (end (snd c) refl))

  rinv (∣ c ⇒ d ∋ ((u , v , f) , ¬μ , p , q) ∣₁ j) i
    with u ⇒ᵐ? v
  -- To satisfy the type-checker we have to spell out the type we are discarding by contradition
  ...| yes μ = absurd {A = PathP (λ j → Path ∣ Crit₀ , Crit₁ ∣
          (hcomp (λ k → (λ {
              (j = i0) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣ p ∣⇝ k))
            ; (j = i1) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣_∣⇝ q k))
            })) (transp (λ _ → ∣ Crit₀ , Crit₁ ∣) i0 (∣ σ u (sink v) (step {u , v , f} μ (v ⇝sink)) j ∣₀)))
          (∣ c ⇒ d ∋ ((u , v , f) , ¬μ , p , q) ∣₁ j))
          (rinv (∣ c ∣₀)) (rinv (∣ d ∣₀))} (¬μ μ) j i
  ...| no ¬μ'
     = hcomp (λ k → λ {
        (i = i0) → compFiller k j
      ; (i = i1) → ∣ c ⇒ d ∋ ((u , v , f) , ¬μ , p , q) ∣₁ j
      ; (j = i0) → ⇝Contr u c p i k
      ; (j = i1) → ⇝Contr v d q i k
      }) (∣ σ u c p i ⇒ σ v d q i
            ∋ ((u , v , f) , ¬μ ,
              ⇝IsHPropS (sink u) c (u ⇝sink) p i ,
              ⇝IsHPropS (sink v) d (v ⇝sink) q i) ∣₁ j)
        where
        transportFiller :
          Path (∣ sink (fst c ) ∣₀ ≡ ∣ sink (fst d ) ∣₀)
            (λ j → hcomp (λ k → (λ {
                (j = i0) → (ϕ (∣ p ∣⇝ k))
              ; (j = i1) → (ϕ (∣_∣⇝ q k))
              })) (∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ¬μ , (u ⇝sink) , (v ⇝sink)) ∣₁  j))
            (λ j → hcomp (λ k → (λ {
                  (j = i0) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣ p ∣⇝ k))
                ; (j = i1) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣_∣⇝ q k))
                })) (transp (λ _ → ∣ Crit₀ , Crit₁ ∣) i0 (∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ¬μ' , (u ⇝sink) , (v ⇝sink)) ∣₁ j)))
        transportFiller i j =
                    hcomp (λ k →
                    λ { (j = i0) → transportRefl (ϕ (∣ p ∣⇝ k)) (~ i ∨ k)
                    ; (j = i1) → transportRefl (ϕ (∣_∣⇝ q k)) (~ i ∨ k)
                    }) (hcomp (λ k →
                    λ { (i = i0) → ∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ⇒ᶜIsHProp ¬μ' ¬μ k , u ⇝sink , v ⇝sink)  ∣₁ j
                      ; (i = i1) → transportRefl ((∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ¬μ' , (u ⇝sink) , (v ⇝sink)) ∣₁ j)) (~ k)
                      ; (j = i0) → transportRefl (∣ sink u ∣₀) (~ i ∨ ~ k)
                      ; (j = i1) → transportRefl (∣ sink v ∣₀) (~ i ∨ ~ k)
                      }) (∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ¬μ' , (u ⇝sink) , (v ⇝sink)) ∣₁ j))

        compFiller : PathP (λ i → Path ∣ Crit₀ , Crit₁ ∣ (ϕ (∣ p ∣⇝ i)) (ϕ (∣_∣⇝ q i)))
          (λ i → ∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ¬μ , (u ⇝sink) , (v ⇝sink)) ∣₁ i)
              λ j → hcomp (λ k →
              (λ {
                (j = i0) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣ p ∣⇝ k))
              ; (j = i1) → transp (λ _ → ∣ Crit₀ , Crit₁ ∣) k (ϕ (∣_∣⇝ q k))
              })
              ) (transp (λ _ → ∣ Crit₀ , Crit₁ ∣) i0 (∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ¬μ' , (u ⇝sink) , (v ⇝sink)) ∣₁ j))
        compFiller = toPathP ((fromPathP (doubleCompPath-filler
                                          (λ i → ϕ (∣ p ∣⇝ (~ i)))
                                          (λ i → ∣ (sink u) ⇒ (sink v) ∋ ((u , v , f) , ¬μ , (u ⇝sink) , (v ⇝sink)) ∣₁ i)
                                          (λ i → ϕ (∣_∣⇝ q i))))
                                        ∙ transportFiller)

  linv : (x : ∣ V , E ∣) → ι (ϕ x) ≡ x

  linv (∣ u ∣₀) = sym (∣ u ⇝sink ∣⇝)

  linv (∣ u ⇒ v ∋ f ∣₁ j) with u ⇒ᵐ? v
  ... | no ¬μ = pqr⁻¹r≡pq (sym ∣ u ⇝sink ∣⇝) ∣ u ⇒ v ∋ f  ∣₁ (sym ∣ v ⇝sink ∣⇝) j
  ... | yes μ = λ i → hcomp (λ k → λ {
     (i = i0) → ∣ isHSet→SquareP (λ i j → V-isHSet)
         (λ _ → (sink v)ᵥ) ρ (sym ρ) (λ _ → (sink v)ᵥ) k j ∣₀
   ; (i = i1) → ∣ u ⇒ v ∋ f  ∣₁ j
   ; (j = i0) → ∣ ⇝IsHPropS (sink u) (sink v)
         (u ⇝sink) (step {u , v , f} μ (v ⇝sink)) (~ k) ∣⇝ (~ i)
   ; (j = i1) → ∣ v ⇝sink ∣⇝ (~ i)
   }) (compPath-filler' ∣ u ⇒ v ∋ f ∣₁ ∣ v ⇝sink ∣⇝ (~ j) (~ i))
   where
   ρ : sink u ᵥ ≡ sink v ᵥ
   ρ = sinkUniq ((sink u) ᵥ) ((sink v) ᵥ) (u ⇝sink) (step {u , v , f} μ (v ⇝sink))

  MorseTheorem : ∣ V , E ∣ ≡ ∣ Crit₀ , Crit₁ ∣
  MorseTheorem = isoToPath (iso ϕ ι rinv linv)

module _ {V : Type ℓ} {E : V → V → Type ℓ} where
  Morse-Program : (G : Graph V E) (μ : Matching G) →
    Σ[ c₀ ∈ Type ℓ ] Σ[ c₁ ∈ (c₀ → c₀ → Type ℓ) ] ∣ V , E ∣ ≡ ∣ c₀ , c₁ ∣
  Morse-Program G μ = Crit₀ , Crit₁ , MorseTheorem
    where open Morse G μ


