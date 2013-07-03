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

∘ Definitions of logical connectives
∘ Properties of logical connectives
∘ Axioms
∘ Some theorems

-}


Proposition = Set

-- TOP

data ⊤ : Proposition where
  true : ⊤

-- BOTTOM

data ⊥ : Proposition where

elim⊥ : {A : Proposition} → ⊥ → A
elim⊥()

-- CONJUNCTION

data _∧_ (A B : Proposition) : Proposition where
  <_,_> : A → B → A ∧ B

elim∧₁ : {A B : Proposition} → A ∧ B → A
elim∧₁ < a , b > = a

elim∧₂ : {A B : Proposition} → A ∧ B → B
elim∧₂ < a , b > = b

-- DISJUNCTION

data _∨_ (A B : Proposition) : Proposition where
  intro∨₁ : A → A ∨ B
  intro∨₂ : B → A ∨ B

elim∨ : {A B C : Proposition} → A ∨ B → (A → C) → (B → C) → C
elim∨ (intro∨₁ x) b c = b x
elim∨ (intro∨₂ x) b c = c x

-- IMPLICATION

data _⊃_ (A B : Proposition) : Proposition where
  intro⊃ : (A → B) → A ⊃ B

elim⊃ : {A B : Proposition} → A ⊃ B → A → B
elim⊃ (intro⊃ x) = x

-- NEGATION

¬ : Proposition → Proposition
¬ A = A → ⊥

-- EQUIVALENCE

_≡_ : Proposition → Proposition → Proposition
A ≡ B = (A ⊃ B) ∧ (B ⊃ A)

-- UNIVERSAL QUANTIFIER

data Forall (A : Set) (B : A → Set) : Proposition where
  intro∀ : ((a : A) → B a) → Forall A B

-- EXISTENTIAL QUANTIFIER

data Exists (A : Set) (B : A → Set) : Proposition where
  intro∃ : (a : A) → B a → Exists A B

-- PROPERTIES

commutativity∧ : {A B : Proposition} → A ∧ B → B ∧ A
commutativity∧ < a , b > = < b , a >

associativity∧ : {A B C : Proposition} → A ∧ (B ∧ C) → (A ∧ B) ∧ C
associativity∧ < a , < b , c > > = < < a , b > , c >

distributivity∧∨ : {A B C : Proposition} → A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
distributivity∧∨ < x , intro∨₁ x₁ > = intro∨₁ < x , x₁ >
distributivity∧∨ < x , intro∨₂ x₁ > = intro∨₂ < x , x₁ >

idempotency∧ : {A : Proposition} → A ∧ A → A
idempotency∧ a = elim∧₁ a

commutativity∨ : {A B : Proposition} → A ∨ B → B ∨ A
commutativity∨ (intro∨₁ x) = intro∨₂ x
commutativity∨ (intro∨₂ x) = intro∨₁ x

associativity∨ : {A B C : Proposition} → A ∨ (B ∨ C) → (A ∨ B) ∨ C
associativity∨ (intro∨₁ x) = intro∨₁ (intro∨₁ x)
associativity∨ (intro∨₂ (intro∨₁ x)) = intro∨₁ (intro∨₂ x)
associativity∨ (intro∨₂ (intro∨₂ x)) = intro∨₂ x

distributivity∨∧ : {A B C : Proposition} → A ∨ (B ∧ C) → (A ∨ B) ∧ (A ∨ C)
distributivity∨∧ (intro∨₁ x) = < intro∨₁ x , intro∨₁ x >
distributivity∨∧ (intro∨₂ < x , y >) = < intro∨₂ x , intro∨₂ y >

idempotency∨ : {A : Proposition} → A ∨ A → A
idempotency∨ (intro∨₁ x) = x
idempotency∨ (intro∨₂ x) = x

distributivity⊃⊃ : {A B C : Proposition} → A ⊃ (B ⊃ C) → (A ⊃ B) ⊃ (A ⊃ C)
distributivity⊃⊃ = {!!}

transitivity⊃ : {A B C : Proposition} → (A ⊃ B) → (B ⊃ C) → (A ⊃ C)
transitivity⊃ = {!!}

reflexivity⊃ : {A : Proposition} → A ⊃ A
reflexivity⊃ = λ {A} → intro⊃ (λ z → z)

totality⊃ : {A B : Proposition} → (A ⊃ B) ∨ (B ⊃ A)
totality⊃ = λ {A} {B} → intro∨₁ (intro⊃  (λ x → {!!}))

distributivity¬∨ : {A B : Proposition} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
distributivity¬∨ = λ x → <  (λ z → x (intro∨₁ z)) , (λ z → x (intro∨₂ z)) >

distributivity¬∧ : {A B : Proposition} → ¬ (A ∧ B) → ¬ A ∨ ¬ B
distributivity¬∧ = λ x → intro∨₁ {!intro∧!}

-- AXIOMS

-- Axiom 1, K combinator

axiom₁ : {A B : Proposition} → A ⊃ (B ⊃ A)
axiom₁ = λ {A} {B} → intro⊃ (λ z → intro⊃ (λ _ → z))

-- Axiom 2, S combinator

axiom₂ : {A B C : Proposition} → (A ⊃ B) ⊃ ((A ⊃ (B ⊃ C)) ⊃ (A ⊃ C))
axiom₂ = λ {A} {B} {C} → intro⊃ (λ x → intro⊃ (λ x₁ → intro⊃ (λ x₂ → {!!})))

-- Axiom 3

axiom₃ : {A B : Proposition} → A ⊃ (B ⊃ (A ∧ B))
axiom₃ = λ {A} {B} → intro⊃ (λ z → intro⊃ (<_,_> z))

-- Axiom 4

axiom₄ : {A B : Proposition} → (A ∧ B) ⊃ A
axiom₄ = λ {A} {B} → intro⊃ (λ x → elim∧₁ x)

-- Axiom 5

axiom₅ : {A B : Proposition} → (A ∧ B) ⊃ B
axiom₅ = λ {A} {B} → intro⊃ (λ x → elim∧₂ x)

-- Axiom 6

axiom₆ : {A B : Proposition} → A ⊃ (A ∨ B)
axiom₆ = λ {A} {B} → intro⊃ intro∨₁

-- Axiom 7

axiom₇ : {A B : Proposition} → B ⊃ (A ∨ B)
axiom₇ = λ {A} {B} → intro⊃ intro∨₂

-- Axiom 8

axiom₈ : {A B C : Proposition} → (A ⊃ C) ⊃ ((B ⊃ C) ⊃ ((A ∨ B) ⊃ C))
axiom₈ = λ {A} {B} {C} → intro⊃ (λ x → intro⊃ (λ x₁ → intro⊃ (λ x₂ → elim∨ x₂ (λ x₃ → elim⊃ x x₃) (λ x₃ → elim⊃ x₁ x₃))))

-- Axiom 9

axiom₉ : {A B C : Proposition} → (A ⊃ B) ⊃ ((A ⊃ ¬ B) ⊃ ¬ A)
axiom₉ = λ {A} {B} {C} → intro⊃ (λ x → intro⊃ (λ x₁ x₂ → elim⊃ (intro⊃ (elim⊃ x₁ x₂)) (elim⊃ x x₂)))

-- Axiom 10

axiom₁₀ : {A B : Proposition} → ¬ A ⊃ (A ⊃ B)
axiom₁₀ = λ {A} {B} → intro⊃ (λ x → intro⊃ (λ x₁ → elim⊥ (x x₁)))

-- Axiom 11

-- universal quantification
-- ∀xA(x) ⊃ A(t)

-- Axiom 12

-- existentional quantification
-- A(t) ⊃ ∃xA(x)

-- SOME THEOREMS

theorem₁ : {A : Proposition} → A → A ∧ ⊤
theorem₁ a = < a , true >

theorem₂ : {A : Proposition} → A ∧ ⊤ → ⊤
theorem₂ < a , true > = true

theorem₃ : {A : Proposition} → A ⊃ ¬ (¬ A)
theorem₃ = λ {A} → intro⊃ (λ x x₁ → x₁ x)
