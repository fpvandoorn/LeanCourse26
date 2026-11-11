-- Name: <insert your name here>

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Function Set

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: **Wednesday**, 18.11.2025 at 16.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

-- Remember the definition Point from last week's assignment: let's parametrise this by a type.
@[ext]
structure Point (α : Type*) where
  x : α
  y : α
  z : α

-- Let's connect this to ℝ³ (i.e. Fin 3 → ℝ).
-- You can use pattern matching to define an element of ℝ³,
-- just like you would for an inductive type.
example {x y z : ℝ} : Fin 3 → ℝ := fun
  | 0 => x
  | 1 => y
  | 2 => z

-- Now prove that Point α and α³ are equivalent.
-- In particular, `Point` from last week and `ℝ³` are equivalent.
example {α : Type*} : (Fin 3 → α) ≃ Point α where
  toFun := fun f ↦ ⟨f 0, f 2, f 1⟩
  invFun P := fun
    | 0 => P.x
    | 1 => P.z
    | 2 => P.y
  left_inv := by
    sorry
  right_inv := by
    sorry

-- Define an equivalence from Fin 2 × Fin 3 to Fin 6.
-- Hint: the tactic `fin_cases x` is useful for variables
-- of the form `x : Fin n`
example : Fin 3 × Fin 2 ≃ Fin 6 :=
  sorry



section EquivalenceRelation

-- Prove that the following defines an equivalence relation.
def integerEquivalenceRelation : Setoid (ℤ × ℤ) where
  r := fun ⟨k, l⟩ ⟨m, n⟩ ↦ k + n = l + m
  iseqv :=
    sorry

/- This simp-lemma will simplify `x ≈ y` in the lemma below. -/
@[simp] lemma integerEquivalenceRelation'_iff (a b : ℤ × ℤ) :
  letI := integerEquivalenceRelation; a ≈ b ↔ a.1 + b.2 = a.2 + b.1 := by rfl

example : Quotient integerEquivalenceRelation ≃ ℤ :=
  sorry

end EquivalenceRelation

section choice

/-- This exercise is about a subtle detail regarding the axiom of choice: while you know there
is a global choice function, it is not given by one "computation rule".
The following exercise makes this precise: prove it.

The key to this exercise is *proof irrelevance*: in Lean, any two proofs
of the same proposition are definitionally equal.
-/
example (choiceFunction : ∀ (α : Type) (p : α → Prop) (_h : ∃ x, p x), α)
    (h : ∀ (α : Type) (p : α → Prop) (x : α) (hx : p x), choiceFunction α p ⟨x, hx⟩ = x) :
    False := by
  sorry


end choice

section

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by
  sorry

-- In the lecture, we also saw injectivity and bijectivity of functions.
-- There is another variant, "bijectivity on a set":
def BijectiveOn {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (f '' s ⊆ t) ∧ InjOn f s ∧ SurjOn f s t

-- There is a curious fact about infinite types: they are bijective to a proper subset.
-- Let us explore this theme in the following exercises.

example : ∃ f : ℕ → ℕ, BijectiveOn f univ (univ \ {0}) := by
  sorry

example {α : Type*} [Infinite α] {a : α} : ∃ f : α → α, BijectiveOn f (univ \ {a}) univ := by
  -- Hint: a useful first step is "there exists an injective map ℕ → α".
  -- Use loogle or exact? to find this.
  sorry

-- In particular, an infinite type is bijective to a proper subtype.
-- If you like a little *challenge*, prove the converse.
-- This is a bit harder; you want to write down a careful mathematical proof first
-- and use loogle to re-use existing results from mathlib.
example {α : Type*} {s : Set α} (hs : s ≠ univ) {f : α → α} (hf : BijectiveOn f s univ) :
    Infinite α := by
  sorry

end



/-! # Exercises to hand-in. -/


noncomputable section choice

variable {α β γ : Type} {f : α → γ} {g : β → γ}

/- In mathematics, we often identify two sets by realizing them as the
same subset of some larger set. Construct, using the axiom of choice,
such an equivalence.
Hint: it might be useful to define auxilliary functions and lemmas that
can be used in the main proof body
-/
example (hf : Injective f) (hg : Injective g) (H : range f = range g) : α ≃ β :=
  sorry

end choice


section Subtypes

/-- Let's prove that the positive rationals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use `apply` to use the lemmas about real numbers. -/

abbrev PosRat : Type := {x : ℚ // 0 < x}


instance groupPosRat : Group PosRat :=
  sorry



end Subtypes


section cardinality

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] Finset.card_powerset
#check Finset.induction

lemma finset_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (Finset.powerset s) = 2 ^ Finset.card s := by
  sorry

end cardinality
