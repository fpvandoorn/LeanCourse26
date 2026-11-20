-- Name: <insert your name here>

module

public import Mathlib.Analysis.Complex.Exponential

open Real Function Set Nat

#click_suggestions

/-

* Hand in the solutions to the exercises below. Deadline: 4.11.2025 before class.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

section calculations

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  sorry

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
  sorry

end calculations

section Min
open LE
variable (a b c d : ℝ)

/- Recall the following properties of the `≤` relation -/
#check (le : ℝ → ℝ → Prop)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)

/- The following theorems characterize `min`.
Let's use this characterization of it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- Note: the tactic `order` proves both of these immediately
-- For practice, prove them "by hand"
lemma exercise_min_comm : min a b = min b a := by
  sorry

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by
  sorry

-- Prove the following exercise. You can use mathlib tactics now.
lemma exercise_min : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  sorry

end Min

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by
  sorry


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
example (p : Prop) : p ∨ ¬ p := by
  sorry

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (132 + 32 * 3, (x + y) ^ 2) = (228, x ^ 2 + 2 * x * y + y ^ 2) := by
  sorry

/- Prove a version of the axiom of choice Lean's `Classical.choose`.

Note: this might be a bit harder; you will probably find `Classical.choose` and
`Classical.choose_spec` useful. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by
  sorry

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by
  sorry

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by
  sorry

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by
  sorry

/- Prove this without using lemmas from Mathlib -/
example {f : α → β} (h : Injective f) : Injective (image f) := by
  sorry

end Set


/-! # Exercises to hand-in. -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext y
  constructor
  · intro h
    obtain ⟨⟨x, hx, hxy⟩, ht⟩ := h
    rw [←hxy] at ht
    have h2 : x ∈ s ∩ f ⁻¹' t :=⟨hx, ht⟩
    exact ⟨x, h2, hxy⟩
  . intro h
    obtain ⟨x, ⟨hx, ht⟩, hxy⟩ := h
    constructor
    · exact ⟨x,hx, hxy⟩
    · have h2 : f x ∈ t := ht
      rw[hxy] at h2
      assumption

/- Prove this without using lemmas from Mathlib. -/
-- Note: we still use the `simp` tactic... which is using mathlib, but only in a mild way.
-- That's a reasonable compromise for now.
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · simp
    intro x X h1 h2
    use X
    exact ⟨x, h1, h2⟩
  · simp
    intro X x h1 h2
    use x
    constructor
    · use X
    · assumption

/- Prove this without using lemmas from Mathlib. -/
example {a b c d : ℝ} (hab : a < b) : Icc a b ⊆ Ioo c d ↔ c < a ∧ b < d := by
  constructor
  · intro h
    constructor
    · have ha : a ∈ Icc a b := by
        refine ⟨?_, ?_⟩
        · linarith
        · linarith
      specialize h ha
      exact h.1
    · have hb : b ∈ Icc a b := by
        refine ⟨?_, ?_⟩
        · linarith
        · linarith
      specialize h hb
      exact h.2
  · intro h
    obtain ⟨h1, h2⟩ := h
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨?_, ?_⟩
    linarith
    linarith

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  -- can't find anything :(
  ext x
  simp
  -- apply?
  constructor
  · intro h
    -- apply?
    sorry
  · sorry


section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  unfold SurjectiveFunction at *
  constructor
  · intro h1 z
    obtain ⟨a, ha⟩ := h1 z
    exact ⟨f a, ha⟩
  · intro h1 z
    obtain ⟨y, h2⟩ := h1 z
    obtain ⟨x, hx⟩ := hf y
    rw[← hx] at h2
    exact ⟨x, h2⟩

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  unfold SurjectiveFunction at *
  simp
  intro x
  use x
  sorry

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  sorry

end Surjectivity
