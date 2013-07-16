module IntuitionisticLogic where

{-

Intuitionistic logic (experiments in Agda)

Copyright (C) 2013  Lev Lamberov <l.lamberov@gmail.com>

This program is licensed under the GNU General Public License (GPL).
you can redistribute it and/or modify it under the terms of the GNU
General Public License as published by the Free Software Foundation,
Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA; either
version 2 of the License, or (at your option) any later version.
Distributions of pympcc should include a copy of the GPL in a
file called COPYING.  The GPL is also available online at
http://www.gnu.org/copyleft/gpl.html.

Notation:
⊤ : top, truth
⊥ : bottom, false
∧ : conjunction
∨ : disjuntion
⊃ : implication
¬ : negation
⇔ : equivalence

Contents:

∘ Imports
∘ Definitions of logical connectives
∘ Properties of logical connectives
∘ Axioms
∘ Admissible rules
∘ Some theorems
∘ References

-}

-- IMPORTS

open import Data.Sum

-- DEFINITIONS OF LOGICAL CONNECTIVES

Proposition = Set

-- Top

data ⊤ : Proposition where
  true : ⊤

-- Bottom

data ⊥ : Proposition where

elim⊥ : {A : Proposition} → ⊥ → A
elim⊥()

-- Conjunction

data _∧_ (A B : Proposition) : Proposition where
  <_,_> : A → B → A ∧ B

elim∧₁ : {A B : Proposition} → A ∧ B → A
elim∧₁ < a , b > = a

elim∧₂ : {A B : Proposition} → A ∧ B → B
elim∧₂ < a , b > = b

-- Disjunction

data _∨_ (A B : Proposition) : Proposition where
  intro∨₁ : A → A ∨ B
  intro∨₂ : B → A ∨ B

elim∨ : {A B C : Proposition} → A ∨ B → (A → C) → (B → C) → C
elim∨ (intro∨₁ x) b c = b x
elim∨ (intro∨₂ x) b c = c x

-- Implication

data _⊃_ (A B : Proposition) : Proposition where
  intro⊃ : (A → B) → A ⊃ B

elim⊃ : {A B : Proposition} → A ⊃ B → A → B
elim⊃ (intro⊃ x) = x

-- Negation

¬ : Proposition → Proposition
¬ A = A → ⊥

-- Equivalence

_≡_ : Proposition → Proposition → Proposition
A ≡ B = (A ⊃ B) ∧ (B ⊃ A)

-- Universal quantifier

data Forall (A : Set) (B : A → Proposition) : Proposition where
  intro∀ : ((a : A) → B a) → Forall A B

elim∀ : {A : Set} {B : A → Proposition} → Forall A B → (t : A) → B t
elim∀ (intro∀ proof-constructor) t = proof-constructor t

-- Existential quantifier

data Exists (A : Set) (B : A → Proposition) : Proposition where
  intro∃ : (a : A) → B a → Exists A B

elim∃ : {A : Set} {B : A → Proposition} → Exists A B → A
elim∃ (intro∃ t proof-of-B[t]) = t

-- PRECEDENCE

infix 10 _≡_
infix 30 _⊃_
infix 50 _∨_
infix 70 _∧_
infix 90 ¬

-- PROPERTIES OF LOGICAL CONNECTIVES

commutativity∧ : {A B : Proposition} → A ∧ B ≡ B ∧ A
commutativity∧ = λ {A} {B} → < (intro⊃ (λ x → < (elim∧₂ x) , (elim∧₁ x) >)) , (intro⊃ (λ x → < (elim∧₂ x) , (elim∧₁ x) >)) >

associativity∧ : {A B C : Proposition} → (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C)
associativity∧ = λ {A} {B} {C} → < (intro⊃ (λ x → < < (elim∧₁ x) , (elim∧₁ (elim∧₂ x)) > , (elim∧₂ (elim∧₂ x)) >)) , (intro⊃ (λ x → < (elim∧₁ (elim∧₁ x)) , < (elim∧₂ (elim∧₁ x)) , (elim∧₂ x) > >)) >

distributivity∧∨ : {A B C : Proposition} → (A ∧ (B ∨ C)) ≡ ((A ∧ B) ∨ (A ∧ C))
distributivity∧∨ = λ {A} {B} {C} → < (intro⊃ (λ x → elim∨ (elim∧₂ x) (λ x₁ → elim∧₁ < (intro∨₁ < (elim∧₁ x) , x₁ >) , x₁ >) (λ x₁ → elim∧₂ < x₁ , (intro∨₂ < (elim∧₁ x) , x₁ >) >))) , intro⊃ (λ x → elim∨ x (λ x₁ → < (elim∧₁ x₁) , (intro∨₁ (elim∧₂ x₁)) >) (λ x₁ → < (elim∧₁ x₁) , (intro∨₂ (elim∧₂ x₁)) >)) >

idempotency∧ : {A : Proposition} → A ∧ A ≡ A
idempotency∧ = λ {A} → < (intro⊃ (λ x → elim∧₁ x)) , (intro⊃ (λ x → < x , x >)) >

commutativity∨ : {A B : Proposition} → A ∨ B ≡ B ∨ A
commutativity∨ = λ {A} {B} → < (intro⊃ (λ x → elim∨ x intro∨₂ intro∨₁)) , (intro⊃ (λ x → elim∨ x intro∨₂ intro∨₁)) >

associativity∨ : {A B C : Proposition} → (A ∨ (B ∨ C)) ≡ ((A ∨ B) ∨ C)
associativity∨ = λ {A} {B} {C} → < (intro⊃ (λ x → {!!})) , (intro⊃ (λ x → {!!})) >

distributivity∨∧ : {A B C : Proposition} → (A ∨ (B ∧ C)) ≡ ((A ∨ B) ∧ (A ∨ C))
distributivity∨∧ = λ {A} {B} {C} → < (intro⊃ (λ x → < (elim∨ x intro∨₁ (λ x₁ → intro∨₂ (elim∧₁ x₁))) , (elim∨ x intro∨₁ (λ x₁ → intro∨₂ (elim∧₂ x₁))) >)) , intro⊃ (λ x → {!!}) >

idempotency∨ : {A : Proposition} → A ∨ A ≡ A
idempotency∨ = λ {A} → < (intro⊃ (λ x → elim∨ x (λ z → z) (λ z → z))) , (intro⊃ (λ x → intro∨₁ x)) >

distributivity⊃⊃ : {A B C : Proposition} → (A ⊃ (B ⊃ C)) ≡ ((A ⊃ B) ⊃ (A ⊃ C))
distributivity⊃⊃ = λ {A} {B} {C} → < (intro⊃ (λ x → intro⊃ (λ x₁ → intro⊃ (λ x₂ → elim⊃ (elim⊃ x x₂) (elim⊃ x₁ x₂))))) , (intro⊃ (λ x → intro⊃ (λ x₁ → intro⊃ (λ x₂ → elim⊃ (elim⊃ x (intro⊃ (λ _ → x₂))) x₁)))) >

transitivity⊃ : {A B C : Proposition} → (A ⊃ B) ⊃ ((B ⊃ C) ⊃ (A ⊃ C))
transitivity⊃ = λ {A} {B} {C} → intro⊃ (λ x → intro⊃ (λ x₁ → intro⊃ (λ x₂ → elim⊃ x₁ (elim⊃ x x₂))))

reflexivity⊃ : {A : Proposition} → A ⊃ A
reflexivity⊃ = λ {A} → intro⊃ (λ z → z)

distributivity¬∨ : {A B : Proposition} → ¬(A ∨ B) ⊃ ¬ A ∧ ¬ B
distributivity¬∨ = λ {A} {B} → intro⊃ (λ x → < (λ x₁ → x (intro∨₁ x₁)) , (λ x₁ → x (intro∨₂ x₁)) >)

-- AXIOMS

-- Axiom 1, K combinator

axiom₁ : {A B : Proposition} → A ⊃ (B ⊃ A)
axiom₁ = λ {A} {B} → intro⊃ (λ z → intro⊃ (λ _ → z))

-- Axiom 2, S combinator

axiom₂ : {A B C : Proposition} → (A ⊃ B) ⊃ ((A ⊃ (B ⊃ C)) ⊃ (A ⊃ C))
axiom₂ = λ {A} {B} {C} → intro⊃ (λ x → intro⊃ (λ x₁ → intro⊃ (λ x₂ → elim⊃ (intro⊃ (λ z → z)) (elim⊃ (elim⊃ x₁ x₂) (elim⊃ x x₂)))))

-- Axiom 3

axiom₃ : {A B : Proposition} → A ⊃ (B ⊃ A ∧ B)
axiom₃ = λ {A} {B} → intro⊃ (λ z → intro⊃ (<_,_> z))

-- Axiom 4

axiom₄ : {A B : Proposition} → A ∧ B ⊃ A
axiom₄ = λ {A} {B} → intro⊃ (λ x → elim∧₁ x)

-- Axiom 5

axiom₅ : {A B : Proposition} → A ∧ B ⊃ B
axiom₅ = λ {A} {B} → intro⊃ (λ x → elim∧₂ x)

-- Axiom 6

axiom₆ : {A B : Proposition} → A ⊃ A ∨ B
axiom₆ = λ {A} {B} → intro⊃ intro∨₁

-- Axiom 7

axiom₇ : {A B : Proposition} → B ⊃ A ∨ B
axiom₇ = λ {A} {B} → intro⊃ intro∨₂

-- Axiom 8

axiom₈ : {A B C : Proposition} → (A ⊃ C) ⊃ ((B ⊃ C) ⊃ (A ∨ B ⊃ C))
axiom₈ = λ {A} {B} {C} → intro⊃ (λ x → intro⊃ (λ x₁ → intro⊃ (λ x₂ → elim∨ x₂ (λ x₃ → elim⊃ x x₃) (λ x₃ → elim⊃ x₁ x₃))))

-- Axiom 9

axiom₉ : {A B C : Proposition} → (A ⊃ B) ⊃ ((A ⊃ ¬ B) ⊃ ¬ A)
axiom₉ = λ {A} {B} {C} → intro⊃ (λ x → intro⊃ (λ x₁ x₂ → elim⊃ (intro⊃ (elim⊃ x₁ x₂)) (elim⊃ x x₂)))

-- Axiom 10

axiom₁₀ : {A B : Proposition} → ¬ A ⊃ (A ⊃ B)
axiom₁₀ = λ {A} {B} → intro⊃ (λ x → intro⊃ (λ x₁ → elim⊥ (x x₁)))

-- Axiom 11

axiom₁₁ : {A : Set} {B : A → Proposition} {t : A} → Forall A (λ x → B x) ⊃ B t
axiom₁₁ = λ {A} {B} {t} → intro⊃ (λ x → elim∀ x t)

-- Axiom 12

axiom₁₂ : {A : Set} {B : A → Proposition} {t : A} → B t ⊃ Exists A (λ x → B x)
axiom₁₂ = λ {A} {B} {t} → intro⊃ (intro∃ t)

-- ADMISSIBLE RULES

-- Gödel's disjunction property (Gödel (1932))
admissible₁ : {A B : Set} → A ∨ B → A ⊎ B
admissible₁ = λ x → elim∨ x inj₁ inj₂

-- Kleene's existence property (Kleene (1945, 1952))
admissible₂ : {A : Set} {B : A → Proposition} → (p : Exists A B) → B (elim∃ p)
admissible₂ (intro∃ a x) = x

-- SOME THEOREMS

-- Brouwer (1919)
theorem₀ : {A : Proposition} → ¬ A ≡ ¬(¬(¬ A))
theorem₀ = λ {A} → < (intro⊃ (λ z z₁ → z₁ z)) , (intro⊃ (λ z z₁ → z (λ z₂ → z₂ z₁))) >

theorem₁ : {A : Proposition} → A ⊃ A ∧ ⊤
theorem₁ = λ {A} → intro⊃ (λ x → < x , true >)

theorem₂ : {A : Proposition} → A ∧ ⊤ ⊃ ⊤
theorem₂ = λ {A} → intro⊃ (λ x → true)

theorem₃ : {A : Proposition} → A ⊃ ¬ (¬ A)
theorem₃ = λ {A} → intro⊃ (λ x x₁ → x₁ x)

theorem₄ : {A : Proposition} → ¬(¬(A ∨ ¬ A))
theorem₄ = λ {A} z → z (intro∨₂ (λ x → z (intro∨₁ x)))

-- REFERENCES

-- Brouwer, L. E. J., 1919, "Intuitionistische Mengenlehre," Jahresber. Dtsch.Math.Ver., 28: 203–208.
-- Gödel, K., 1932, "Zum intuitionistischen Aussagenkalkül," Anzeiger der Akademie der Wissenschaftischen in Wien 69: 65–66.
-- Kleene, S. C., 1945, "On the interpretation of intuitionistic number theory," Jour. Symb. Logic, 10: 109–124.
-- Kleene, S. C., 1952, Introduction to Metamathematics, Princeton: Van Nostrand.
