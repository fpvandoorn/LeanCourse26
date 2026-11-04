module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.FieldTheory.Finite.Basic

noncomputable section

#click_suggestions


/-
## Practical Remarks
* See the `Projects` for a description of the two projects.
  First deadline (for both projects) on Nov 18.

-/

/-
## Last time

Last time we saw:

* Sets:
  - `Set α` is the type of sets with elements from `α`.
  - Common notation can be used: `x ∈ s`, `s ⊆ t`, `s ∪ t`, `∅`, ...
  - Prove two sets equal by using the `ext` tactic.
  - We can use the notation `{x : α | P x}`
    for the set of elements satisfying `P`.
  - Unions/intersections: `⋃ i : ι, C i`, `⋃ i ∈ s, C i` or `⋃₀ C`.
  - preimages `f ⁻¹' s` and images `f '' t` of sets.
  - point-wise operations (e.g. the Minkowski sum).
  - writing enumerated sets `{1, 2, 3} : Set ℝ`.
* intervals: `Icc` and friends
  - "c" = closed, "o" = open, "i" = infinite
  - e.g., `Set.Ici a b = [a, ∞)` for `a b : ℝ`
  - e.g., `Set.Iio b   = (-∞, b)`
* useful tactics for dealing with numbers:
  - `norm_num`: compute equalities and inequalities involving numerals
  - `lia` can do linear arithmetic on `ℕ` and `ℤ`
  - `positivity`: can show that something is positive/non-negative/nonzero
  - `field_simp` can simplify divisions.
* warning: subtraction and division of natural numbers returns a natural number!
* coercions (e.g., `(12 : ℚ) / 15` interprets 12 as a rational number),
  shown as `↑` in the infoview
* `norm_cast` pulls coercions out of an expression (e.g., turn `↑n * ↑m` into `↑(n * m)`),
  `push_cast` pushes them inside (e.g., turn `↑(n + m)` into `↑n + ↑m`)
-/


/-
# Today: recursion and induction
-/

/-
Let's start by defining our own factorial function.
Note that there is no `:=` in this syntax.
-/

def fac : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fac n


lemma fac_zero : fac 0 = 1 := by rw [fac]

lemma fac_succ (n : ℕ) :
    fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

example : fac 4 = 24 := by rfl

#eval fac 100




/-
Lean checks that every function is *terminating*. If it isn't,
you have to mark it `partial` and cannot use it in proofs.
-/
partial def wrong : ℕ → ℕ
  | n => 1 + wrong (n + 1)

example (n : ℕ) : wrong n ≠ 0 := by
  sorry -- impossible to prove




/-
You can also use `partial_fixpoint` to define partial functions.
This gives a function that satisfies the defining equation, and
you can reason with it, even if its value is not uniquely defined
for every input.
-/
def find (p : ℕ → Bool) (i : ℕ) : ℕ :=
  if p i then
    i
  else
    find p (i + 1)
partial_fixpoint

example (p : ℕ → Bool) (i : ℕ) (h : p i) : find p i = i := by
  simp [find, h]





/- ## Induction -/

/-
Let's prove that the factorial function we just defined
is always positive.
-/

lemma fac_pos (n : ℕ) : 0 < fac n := by
  induction n with
  | zero => rw [fac]
            norm_num
  | succ n ih =>
    rw [fac]
    positivity






/- Next we define the Fibonacci numbers.
We mark it with `@[simp]`: this is an *attribute* that tells
the `simp` tactic to simplify its definition whenever it can.
-/

@[simp]
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by
  simp




lemma fib_add (n m : ℕ) :
    fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    calc fib (m + (n + 1) + 1) =
      fib ((m + 1) + n + 1) := by congr 1; ring
      _ = fib (m + 1) * fib n + fib ((m + 1) + 1) * fib (n + 1) := by rw [ih (m + 1)]
      _ = fib m * fib (n + 1) + fib (m + 1) * fib (n + 1 + 1) := by simp; ring

open Finset
/- We can use `∑ i ∈ range n, f i` to take the sum
`f 0 + f 1 + ⋯ + f (n - 1)`. -/

#eval ∑ i ∈ range 11, i ^ 2

example (f : ℕ → ℝ) : ∑ i ∈ range 0, f i = 0 := by
  simp

example (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), f i = (∑ i ∈ range n, f i) + f n :=
  sum_range_succ f n

/-
Here `range n` or `Finset.range n` is the set `{0, ..., n - 1}`.
Its type is `Finset ℕ`, which is a finite set of natural numbers.
We will talk more about finite sets in a later lecture.
-/

#check Finset.range





/- We will prove the basic equality:
`0 + 1 + ⋯ + n = n(n+1)/2`.

Note that we prove the following after coercing to rational numbers.
We could also prove it in `ℕ` (with natural number division),
but it is more annoying to work with natural number division. -/

example (n : ℕ) :
    ∑ i ∈ range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>

    calc ∑ i ∈ range (n + 1 + 1), (i : ℚ) =
      ∑ i ∈ range (n + 1), (i : ℚ) + (n + 1) := by rw [sum_range_succ]; norm_cast
      _ = (n * (n + 1) / 2) + (n + 1 : ℚ) := by rw [ih]
      _ = (↑(n + 1) : ℚ) * (↑(n + 1) + 1) / 2 := by push_cast; ring







/- We can use other induction principles with
`induction ... using ... with`.
There are multiple other induction principles we can use.
-/

/- Prove something by induction with two base cases. -/
#check Nat.twoStepInduction

/- Prove something by strong induction: prove it for `n`
assuming it holds for all numbers below `n`. -/
#check Nat.strongRec

/- Induction with a different starting point:
prove something for all `n ≥ m` by proving it for `m`
and proving it for `k + 1` if it holds for `k`. -/
#check Nat.le_induction


lemma fac_dvd_fac (n m : ℕ) (h : n ≤ m) : fac n ∣ fac m := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hmn ih =>
    rw [fac]
    exact Nat.dvd_mul_left_of_dvd ih (m + 1)

-- END OF LECTURE HERE


/-
Here are two exercises.
-/

example (f : ℕ → ℕ) (hf0 : f 0 = 0)
    (hfs : ∀ n, f (n + 1) = 2 * f n + 1) :
    ∀ n, f n + 1 = 2 ^ n := by
  sorry



/-
Let's prove an explicit formula for the Fibonacci sequence.
We will define the golden ratio, and prove 3 simple properties for you.
These lemmas are marked `@[simp]`, so that `simp` automatically uses them.
-/

open Real

def ϕ : ℝ := (1 + √5) / 2
def ψ : ℝ := (1 - √5) / 2

@[simp] lemma ϕ_sub_ψ_ne_zero : ϕ - ψ ≠ 0 := by
  simp [ϕ, ψ, sub_eq_zero, div_left_inj',
    sub_eq_add_neg (1 : ℝ), CharZero.eq_neg_self_iff]

@[simp] lemma ϕ_sq : ϕ ^ 2 = ϕ + 1 := by
  simp [ϕ, add_sq, div_pow]; ring

@[simp] lemma ψ_sq : ψ ^ 2 = ψ + 1 := by
  simp [ψ, sub_sq, div_pow]; ring


lemma coe_fib_eq (n : ℕ) : (fib n : ℝ) = (ϕ ^ n - ψ ^ n) / (ϕ - ψ) := by
  sorry
