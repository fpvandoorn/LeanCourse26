-- Name: <insert your name here>
import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Finite.Basic

open Real Function Set Nat

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: 28.10.2025 at 16:00.
* Solutions from the section `Exercises to hand-in` will receive feedback
  from the tutors.
* None of your solutions should be LLM-generated: doing so will only rob you
  of the practice and waste the tutors' time.
* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (p q r s : Prop) (h : p ∧ q → r) (hp : p) (h' : q → s) : q → r ∧ s := by
  sorry

example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by
  sorry

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  sorry

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by
  sorry


/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
  sorry


/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by
  sorry

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun _ : ℕ ↦ a) a := by
  sorry

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  sorry

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by
  sorry

-- Use `rw?` or `#click_suggestions` to help you in the following calculation.
-- Alternatively, write out a calc block by hand.
example {G : Type*} [Group G] {a b c : G}
    (h : a⁻¹ * b * c * c⁻¹ * a * b⁻¹ * a * a⁻¹ = b) (h' : b * a = a * b) : b = 1 := by
  sorry

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  sorry


/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
  sorry

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  sorry



/-! # Exercises to hand-in. -/

section Logic
-- Prove the following statements with basic tactics,
-- in particular without using `tauto`, `grind` or lemmas from Mathlib.

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ) := ∀ x, ContinuousAtPoint f x

-- Exercise for you. Remember that you can use `unfold` to expand a definition.
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
    unfold Continuous'
    constructor
    intro hf x
    rw[← hfg x]
    exact hf x
    intro hg x
    rw[hfg x]
    exact hg x

def All (p : ℝ → Prop) := ∀ x, p x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    All p ↔ All q := by
  unfold All
  constructor
  · intro hf x
    rw[← h x]
    exact hf x
  · intro hg x
    rw[h x]
    exact hg x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    (∃ x, p x) ↔ (∃ x, q x) := by
    constructor
    · intro hf
      obtain ⟨x, hfp⟩ := hf
      rw[h] at hfp
      exact ⟨x, hfp⟩
    · intro hg
      obtain ⟨x, hfq⟩ := hg
      rw[← h] at hfq
      exact ⟨x, hfq⟩


-- Is the following true? If yes, prove it in Lean.
-- If not, give a counterexample and prove it. (What do you have to do to do so?)
example (p q : ℕ → Prop) (h: (∃ x, p x) ↔ (∃ x, q x)) : ∀ x, p x ↔ q x := by
  sorry
  -- this is false, for the counterexample i struggeled to get the syntax right for the example


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro hf
    obtain ⟨x, hfp⟩ := hf
    obtain hfp1 | hfp2 := hfp
    · left
      exact ⟨x, hfp1⟩
    · right
      exact ⟨x, hfp2⟩
  · intro hg
    obtain hg1 | hg2 := hg
    · obtain ⟨x, hgg⟩ := hg1
      use x
      left
      exact hgg
    · obtain ⟨x, hgg⟩ := hg2
      use x
      right
      exact hgg

end Logic

section Functions

-- Let us investigate the function example from the lecture further.

-- This is how to say "a natural number p is prime" in Mathlib.
#check Nat.Prime

-- The following theorem is the key ingredient to it.
-- (You have not seen the syntax `[hp: Fact (Nat.Prime p)]` yet:
-- this is related to implicit arguments.
-- You can assume it says `(hp: Nat.Prime p)`. We will discuss the precise difference later.)
--
-- Use `exact?`, `apply?` or `#click_suggestions` to find this theorem in Mathlib.
-- Describe what you are doing.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x := by
  -- exact?
  exact ZMod.pow_card x

-- The above theorem has a name. What is it?
-- Use this name to find the same result using leansearch.net.
-- Describe every step you're performing.

-- We go to the definition of `ZMod.pow_card`: hover over the theorem,
-- right-click and select "Go to definition".
-- This opens the Mathlib file where this theorem is proven. The theorem's doc-string says
-- "/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/".
-- This is the name of the theorem: Fermat's little theorem.

-- We open leansearch.net, type "Fermat's little theorem" as a query and press search.
-- The fourth result we get is `ZMod.pow_card x`, with the description
-- "Fermat's Little Theorem in Z/pZ: x^p=x"


-- Use `exact?` to find the following theorem in Mathlib.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (k : ZMod p) (hk : k ≠ 0) : k ^ (p - 1) = 1 := by
  -- exact?
  exact ZMod.pow_card_sub_one_eq_one hk

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] :
    (fun x ↦ x ^ p + 2 * x ^ (2 * (p - 1) + 1) : ZMod p → ZMod p) = (fun x ↦ 3 * x) := by
  ext x
  rw[ZMod.pow_card x]
  have h : x ^ (2 * (p - 1) + 1) = x := by
    by_cases h : x = 0
    · rw[h, pow_succ, mul_zero]
    · rw[pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one]
      · rw[one_pow, one_mul]
      · exact h
  rw[h]
  ring

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (3 * (p - 1) + 1) = k := by
  by_cases h : k = 0
  · rw[h, pow_succ, mul_zero]
  · rw[pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one]
    · rw[one_pow, one_mul]
    · exact h

example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (5 * (p - 1) + 1) = k := by
  by_cases h : k = 0
  · rw[h, pow_succ, mul_zero]
  · rw[pow_succ, pow_mul', ZMod.pow_card_sub_one_eq_one]
    · rw[one_pow, one_mul]
    · exact h

end Functions


/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by
  unfold SequentialLimit
  unfold SequentialLimit at hs
  unfold SequentialLimit at ht
  intro ε hε
  have hε2 : ε / 2 > 0 := by
    apply half_pos
    exact hε
  have h := hs (ε/2) hε2
  obtain ⟨N, hN⟩ := h
  have h2 := ht (ε/2) hε2
  obtain ⟨M, hM⟩ := h2
  let N_0 := max M N
  use N_0
  intro n hn
  specialize hN n (le_trans (Nat.le_max_right M N) hn)
  specialize hM n (le_trans (Nat.le_max_left M N) hn)
  calc |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring_nf
    _ ≤ |s n - a| + |t n - b| := by exact abs_add_le (s n - a) (t n - b)
    _ < ε := by linarith

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  unfold SequentialLimit at hs
  unfold SequentialLimit
  by_cases h : c = 0
  · rw[h, zero_mul]
    intro ε hε
    use 0
    intro n hn
    simp [hε]
  · intro ε hε
    sorry

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by
  have hm : m^2 ≥0 := by exact sq_nonneg m
  have hk : k^ 2 ≥ 0:= by exact sq_nonneg k
  calc n +1 ≤2- m^2 + 1 := by linarith
    _ ≤ 3 := by linarith
    _ ≤ 3 + k^2 := by linarith


section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  unfold EventuallyGrowsFaster
  intro k
  use k
  intro n hn
  exact?

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  unfold EventuallyGrowsFaster
  unfold EventuallyGrowsFaster at h₁
  unfold EventuallyGrowsFaster at h₂
  intro k
  use k
  intro n hn
  sorry


/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
    unfold EventuallyGrowsFaster
    use Nat.factorial
    constructor
    · intro k
      use k
      intro n hn
      calc k * Nat.factorial n≤ n*Nat.factorial n := by
            apply mul_le_mul_of_nonneg_right
            · exact hn
            · exact Nat.zero_le (Nat.factorial n)
        _ ≤ (n+1)*Nat.factorial n := by
            apply mul_le_mul_of_nonneg_right
            · linarith
            · exact Nat.zero_le (Nat.factorial n)
        _ = Nat.factorial (n+1) := by rw[Nat.factorial_succ]
    · intro n
      exact Nat.factorial_ne_zero n
end Growth
