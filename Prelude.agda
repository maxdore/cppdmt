

{-# OPTIONS --cubical --guardedness --safe  #-}
module Prelude where

open import Cubical.Foundations.Prelude renaming (isProp to isHProp ; isSet to isHSet)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function  -- hiding (_∘_)
open import Cubical.Foundations.Path

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Sum hiding (map) renaming (rec to srec)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₀' ℓ₁' : Level


¬Type_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬Type P = P → ⊥

⊤Prop : hProp ℓ
⊤Prop = Unit* , (λ _ _ _ → tt*)
⊥Prop : hProp ℓ
⊥Prop = (⊥* , isProp⊥*)

hProp→hSet : hProp ℓ → hSet ℓ
hProp→hSet (A , p) = A , isOfHLevelSuc 1 p

⊤Set : hSet ℓ
⊤Set = hProp→hSet ⊤Prop
⊥Set : hSet ℓ
⊥Set = hProp→hSet ⊥Prop

-- the library's isTotal is the truncated version without the x ≢ y premise,
-- so we hide it in favour of the definition below
open BinaryRelation hiding (isTotal)

isIrreflexive : {A : Type ℓ₀} → Rel A A ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isIrreflexive {A = X} R = (x : X) → ¬Type (R x x)

isTotal : {A : Type ℓ₀} → Rel A A ℓ₁ → Type (ℓ-max ℓ₀ ℓ₁)
isTotal {A = X} R = (x y : X) → ¬Type (x ≡ y) → (R x y) ⊎ (R y x)

hProp→Poset : hProp ℓ → Poset ℓ ℓ
hProp→Poset (A , isHProp) = poset A (λ _ _ → Unit*) (isposet (isProp→isSet isHProp)
  (λ _ _ _ _ _ → tt*) (λ _ → lift tt) (λ _ _ _ _ _ → lift tt) λ a b p q → isHProp a b)

⊤Poset : Poset ℓ ℓ
⊤Poset = hProp→Poset ⊤Prop
⊥Poset : Poset ℓ ℓ
⊥Poset = hProp→Poset ⊥Prop


≡⇒≤ : ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → {x y : P} → x ≡ y → x ≤ y
≡⇒≤ (P , (posetstr _≤_ Pstr)) {x = x} p = subst (λ z → x ≤ z) p (is-refl x)
  where
  open IsPoset Pstr

∣_∣ₚ : Poset ℓ₀ ℓ₁ → Type ℓ₀
∣ P ∣ₚ = fst P

isMonotonic : (P Q : Poset ℓ₀ ℓ₁) → (∣ P ∣ₚ → ∣ Q ∣ₚ) → Type (ℓ-max ℓ₀ ℓ₁)
isMonotonic (P , (posetstr _≤P_ Pstr)) (Q , (posetstr _≤Q_ Qstr)) f = ((x y : P) → x ≤P y → f x ≤Q f y)

PosetMap : (P : Poset ℓ₀ ℓ₀') (Q : Poset ℓ₁ ℓ₁') → Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') (ℓ-max ℓ₁ ℓ₁'))
PosetMap (P , posetstr _≤P_ _) (Q , posetstr _≤Q_ _) = Σ[ F ∈ (P → Q) ] ((x y : P) → x ≤P y → F x ≤Q F y)


≤P :  ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → P → P → Type ℓ₁
≤P (P , (posetstr _≤_ Pstr)) x y = x ≤ y

syntax ≤P P x y = x ≤[ P ] y

pstr : ((P , (posetstr _≤_ Pstr)) : Poset ℓ₀ ℓ₁) → IsPoset _≤_
pstr P = PosetStr.isPoset (snd P)

P-max : ((P , _) : Poset ℓ₀ ℓ₁) → P → Type (ℓ-max ℓ₀ ℓ₁)
P-max {_} {_} (P , posetstr _≤_ _) x = (∀ y → y ≤ x)

P-min : ((P , _) : Poset ℓ₀ ℓ₁) → P → Type (ℓ-max ℓ₀ ℓ₁)
P-min {_} {_} (P , posetstr _≤_ _) x = (∀ y → x ≤ y)


PosetInitial : ((P , _) : Poset ℓ₀ ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
PosetInitial {_} {_} (P , posetstr _≤_ _) = Σ[ x ∈ P ] (∀ y → x ≤ y)

PosetTerminal : ((P , _) : Poset ℓ₀ ℓ₁) → Type (ℓ-max ℓ₀ ℓ₁)
PosetTerminal {_} {_} (P , posetstr _≤_ _) = Σ[ x ∈ P ] (∀ y → y ≤ x)


_↔_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

infix 10 _↔_


Dec× : {A : Type ℓ₀} {B : Type ℓ₁} → Dec A → Dec B → Dec (A × B)
Dec× (yes p) (yes q) = yes (p , q)
Dec× (yes p) (no ¬q) = no (λ (a , b) → ¬q b)
Dec× (no ¬p) (yes q) = no (λ (a , b) → ¬p a)
Dec× (no ¬p) (no ¬q) = no (λ (a , b) → ¬q b)

Dec¬ : {A : Type ℓ} → Dec A → Dec (¬ A)
Dec¬ (yes p) = no (λ q → q p)
Dec¬ (no ¬p) = yes ¬p

-- Some renamings to ease legibility of proofs in the paper
_≢_ : {A : Type ℓ} (a b : A) → Type ℓ
a ≢ b = ¬ (a ≡ b)

⊤ = Unit
isHProp⊤ = isPropUnit
isHProp⊥ = isProp⊥
⊤Group = UnitGroup₀
l⊤GroupIso = lUnitGroupIso
_≅_ = GroupIso
_∙≅_ = compGroupIso
infixl 10 _∙≅_
_×G_ = DirProd
infixl 50 _×G_
_×≅_ = GroupIsoDirProd



module _ {A : Type ℓ} {w x y z : A} where
  pqr⁻¹r≡pq : (p : w ≡ x) (q : x ≡ z) (r : y ≡ z)
    → PathP (λ i → (p ∙∙ q ∙∙ sym r) i ≡ q i) p r
  pqr⁻¹r≡pq p q r i j = hcomp (λ k → λ {
    (i = i0) → p (j ∨ ~ k)
    ; (i = i1) → r (j ∨ ~ k)
    ; (j = i1) → q i
    }) (q i)



-- Sides of a square: data type for more convenient reasoning

data Side : Type where
  tp bt lf rt : Side

toB : Side → Bool × Bool
toB tp = false , false
toB bt = false , true
toB lf = true  , false
toB rt = true  , true

frB : Bool × Bool → Side
frB (false , false) = tp
frB (false , true)  = bt
frB (true  , false) = lf
frB (true  , true)  = rt

frB-toB : (i : Side) → frB (toB i) ≡ i
frB-toB tp = refl
frB-toB bt = refl
frB-toB lf = refl
frB-toB rt = refl

toB-inj : {i j : Side} → toB i ≡ toB j → i ≡ j
toB-inj {i} {j} p = sym (frB-toB i) ∙ cong frB p ∙ frB-toB j

Side-discrete : Discrete Side
Side-discrete i j =
  mapDec toB-inj (λ ¬p q → ¬p (cong toB q))
  (discreteΣ _≟_ (λ _ → _≟_) (toB i) (toB j))

Side-isHSet : isHSet Side
Side-isHSet = Discrete→isSet Side-discrete

-- a canonical side different from a given one (used to build gradient steps)
otherSide : Side → Side
otherSide tp = bt
otherSide bt = tp
otherSide lf = rt
otherSide rt = lf

otherSide≢ : (i : Side) → ¬ otherSide i ≡ i
otherSide≢ tp p = true≢false (cong (snd ∘ toB) p)
otherSide≢ bt p = false≢true (cong (snd ∘ toB) p)
otherSide≢ lf p = true≢false (cong (snd ∘ toB) p)
otherSide≢ rt p = false≢true (cong (snd ∘ toB) p)

--------------------------------------------------------------------------------
-- The sides of a square are pairwise distinct

private
  fstNe : {i j : Side} → ¬ (fst (toB i) ≡ fst (toB j)) → ¬ (i ≡ j)
  fstNe h p = h (cong (λ x → fst (toB x)) p)

  sndNe : {i j : Side} → ¬ (snd (toB i) ≡ snd (toB j)) → ¬ (i ≡ j)
  sndNe h p = h (cong (λ x → snd (toB x)) p)

bt≢tp : ¬ (bt ≡ tp)
bt≢tp = sndNe true≢false
lf≢tp : ¬ (lf ≡ tp)
lf≢tp = fstNe true≢false
rt≢tp : ¬ (rt ≡ tp)
rt≢tp = fstNe true≢false

tp≢bt : ¬ (tp ≡ bt)
tp≢bt = sndNe false≢true
lf≢bt : ¬ (lf ≡ bt)
lf≢bt = fstNe true≢false
rt≢bt : ¬ (rt ≡ bt)
rt≢bt = fstNe true≢false

tp≢lf : ¬ (tp ≡ lf)
tp≢lf = fstNe false≢true
bt≢lf : ¬ (bt ≡ lf)
bt≢lf = fstNe false≢true
rt≢lf : ¬ (rt ≡ lf)
rt≢lf = sndNe true≢false

tp≢rt : ¬ (tp ≡ rt)
tp≢rt = fstNe false≢true
bt≢rt : ¬ (bt ≡ rt)
bt≢rt = fstNe false≢true
lf≢rt : ¬ (lf ≡ rt)
lf≢rt = sndNe false≢true



--------------------------------------------------------------------------------
-- Filling a square when three of its four sides are known
--
-- The missing side is then uniquely determined, and so is the filler: the type
-- of "fourth side together with a square on it" is contractible.  This little
-- observation is the whole of the collapse in dimension two.  Because it is a
-- statement about a *contractible* type, it applies not only to build the
-- collapsing map but, one dimension up, to build the homotopy witnessing that
-- the collapse is an equivalence — which is why no h-level ever has to grow.

module _ {A : Type ℓ} {a b c d : A} where

  contrBot : (qt : a ≡ b) (ql : a ≡ c) (qr : b ≡ d)
    → isContr (Σ[ qb ∈ c ≡ d ] Square qt qb ql qr)
  contrBot qt ql qr = isContrSinglP (λ i → ql i ≡ qr i) qt

  contrTop : (qb : c ≡ d) (ql : a ≡ c) (qr : b ≡ d)
    → isContr (Σ[ qt ∈ a ≡ b ] Square qt qb ql qr)
  contrTop qb ql qr = isContrRetract
    (λ (x , p) → x , symP p) (λ (x , p) → x , symP p) (λ _ → refl)
    (isContrSinglP (λ i → ql (~ i) ≡ qr (~ i)) qb)

  contrRight : (qt : a ≡ b) (qb : c ≡ d) (ql : a ≡ c)
    → isContr (Σ[ qr ∈ b ≡ d ] Square qt qb ql qr)
  contrRight qt qb ql = isContrRetract
    (λ (x , p) → x , flipSquare p) (λ (x , p) → x , flipSquare p) (λ _ → refl)
    (isContrSinglP (λ i → qt i ≡ qb i) ql)

  contrLeft : (qt : a ≡ b) (qb : c ≡ d) (qr : b ≡ d)
    → isContr (Σ[ ql ∈ a ≡ c ] Square qt qb ql qr)
  contrLeft qt qb qr = isContrRetract
    (λ (x , p) → x , symP (flipSquare p)) (λ (x , p) → x , flipSquare (symP p)) (λ _ → refl)
    (isContrSinglP (λ i → qt (~ i) ≡ qb (~ i)) qr)
