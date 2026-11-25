-- Name: <Maria Sauerhering und Mia Deißler>

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
  calc
    t^2-3*t-17 = t*t-3*t-17 := by ring
    _≥ 10*t-3*t-17 := by gcongr
    _= 7*t-17 := by ring
    _≥ 7*10-17 := by gcongr
    _= 53 := by ring
    _≥ 5 := by norm_num

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
    calc
      t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = (t^2-4)*(t^2+3*t+1)+10*t+2:= by ring
      _= 0*(t^2+3*t+1)+10*t+2:= by rw[ht]
      _= 10*t+2 := by ring

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
  have h1: min a b ≤ a := by
    apply min_le_left
  have h2: min b a ≤ a := by
    apply min_le_right
  apply le_antisymm
  · apply le_min
    · exact min_le_right a b
    · exact h1
  · apply le_min
    · exact h2
    · exact min_le_left b a

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by
  --have h1 : min (min a b) c ≤ min a b := by
    --apply min_le_left
  --have h2 : min b c ≤ b := by
    --apply min_le_left
  apply le_antisymm
  · apply le_min
    · apply le_min
      · exact min_le_left a (min b c)
      · apply le_trans (min_le_right a (min b c))
        exact min_le_left b c
    · apply le_trans (min_le_right a (min b c))
      exact min_le_right b c
  · apply le_min
    · apply le_trans (min_le_left (min a b) c)
      exact min_le_left a b
    · apply le_min
      · apply le_trans (min_le_left (min a b) c)
        exact min_le_right a b
      · apply le_trans (min_le_right (min a b) c)
        apply le_refl

-- Prove the following exercise. You can use mathlib tactics now.
lemma exercise_min : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  order

end Min

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by
  constructor
  · intro h a
    rw[h]
    exact?
  · intro h
    ext x1
    constructor
    · intro h1
      exact?
    · intro h2
      exact?


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
example (p : Prop) : p ∨ ¬ p := by
  by_contra h
  apply h
  right
  intro hp
  apply h
  left
  assumption

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
  ext
  · simp
  · simp
    exact?

/- Prove a version of the axiom of choice Lean's `Classical.choose`.

Note: this might be a bit harder; you will probably find `Classical.choose` and
`Classical.choose_spec` useful. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by
  use fun i => Classical.choose (hC i)
  intro i
  exact Classical.choose_spec (hC i)

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by
  intro a h
  simp at *
  obtain ⟨b, h2, h3⟩ := h
  rw[h3] at h2
  assumption

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by
  unfold Surjective at h
  intro a h2
  obtain ⟨b, h3⟩ := h a
  use b
  constructor
  · rw [@mem_preimage]
    rw[← h3] at h2
    assumption
  · assumption


example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  unfold Injective at h
  intro b h1
  obtain ⟨h2, h3⟩ := h1
  simp at *
  obtain ⟨a, h4, h5⟩ := h2
  use a
  obtain ⟨a_1, h6, h7⟩ := h3
  constructor
  · constructor
    · assumption
    · have h8 : a = a_1 := by
        apply h
        rw[← h7] at h5
        assumption
      rw[← h8] at h6
      assumption
  · assumption


example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  · intro h
    obtain ⟨y, h2, h3⟩ := h
    sorry
  · sorry


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
    simp at *
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x, hh2⟩ := h1
    use x
    obtain ⟨hhh1, hhh2⟩ := hh2
    constructor
    · constructor
      · assumption
      · rw[hhh2]
        assumption
    · assumption
  · intro h
    simp at *
    obtain ⟨x, h1⟩ := h
    obtain ⟨h2, h3⟩ := h1
    obtain ⟨h4, h5⟩ := h2
    constructor
    · use x
    · rw[← h3]
      assumption

/- Prove this without using lemmas from Mathlib. -/
-- Note: we still use the `simp` tactic... which is using mathlib, but only in a mild way.
-- That's a reasonable compromise for now.
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · intro h
    simp at*
    obtain ⟨x, h1, h2⟩ := h
    obtain ⟨i, h3⟩ := h1
    use i
    --exact ⟨x, h3, h2⟩
    use x
  · intro h
    simp at *
    obtain ⟨i, x, h1, h2⟩ := h
    use x
    constructor
    · use i
    · assumption

/- Prove this without using lemmas from Mathlib. -/
example {a b c d : ℝ} (hab : a < b) : Icc a b ⊆ Ioo c d ↔ c < a ∧ b < d := by
  constructor
  · intro h
    constructor
    · sorry
    · sorry
  · intro h
    obtain ⟨hca, hbd⟩ := h
    sorry

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  ext x
  constructor
  · intro h
    simp at *
    by_cases hx : x ≤ -4
    · left
      assumption
    · right
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
  simp at *
  constructor
  · intro h1 y
    obtain ⟨x, h2⟩ := h1 y
    use f x
  · intro h1 z
    obtain ⟨y, h2⟩ := h1 z
    obtain ⟨x, h3⟩ := hf y
    use x
    rw[h3]
    assumption

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  unfold SurjectiveFunction at *
  simp at *
  intro y
  obtain ⟨x, h1⟩ := hf ((y-1)/2)
  use (x-12)/3
  ring
  rw[h1]
  ring


/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  unfold Surjective
  let R := {x | x ∉ f x}
  intro h
  obtain ⟨a, ha⟩ := h R
  by_cases hm : a ∈ f a
  have h1 : a ∈ R := by
    rw[ha] at hm
    assumption
  exact h1 hm
  have h1 : a ∈ R := hm
  rw [← ha] at h1
  exact hm h1

end Surjectivity
