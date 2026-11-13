import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Nat
open Real (exp sin continuous_sin exp_le_exp)
noncomputable section
variable (a b : ℝ)




/-
# Practical remarks
* *We will add a third (and maybe fourth?) exercise session. Details TBA.*
* The lecture file will be posted in advance of class,
  so you can read along during class.
* To get the latest version of this repository,
  follow the instructions in the README file.
  (if you have issues, ask a tutor)
-/







/- # Last Week -/

/- You type code on the left-hand side of the screen,
and Lean automatically compiles the file and
shows output in the *Lean Infoview* on the right.

If you ever close the Infoview, you can toggle it
under the `∀`-button at the top-right of your window. -/



/- Every expression in Lean has a type. -/

#check 1
#check fun x : ℝ ↦ x^2

/- The type `Prop` contains all statements -/


#check Nat.Prime 3
#check Nat.Prime 4




/- Nat.Prime is a predicate on natural numbers,
so it has type `ℕ → Prop`. -/

#check (Nat.Prime)
#check Nat.Prime







/- What is the type of the factorial function? -/
-- #check (Nat.factorial)
-- #check fun n ↦ n !



/- What is the type of the predicate
stating that a real number is less than π? -/
-- #check fun x : ℝ ↦ x < π


/- What is the type of addition on the natural numbers? -/
-- #check fun n m : ℕ ↦ n + m



/- What is the type of `≤` on the integers? -/
-- #check fun n m : ℤ ↦ n ≤ m







/- ## rfl -/

/- If we have a statement `A : Prop`,
we can try to prove `A` using *tactics*.

The easiest tactic is **`rfl`**, which shows that an
equality holds where both sides are literally the same.

It can also unfold definitions. -/


example (a b c : ℝ) : a * b + c = a * b + c := by
  sorry


example : 4! = 24 := by
  sorry







/- ## ring -/

/- A much more powerful tactic is the **`ring`** tactic,
which will prove anything that only requires the axioms of a ring.
So it can reason with `+`, `-`, `*`, and natural number exponents,
but not with other operations (like division). -/

example (a b : ℝ) : a * (a + b) = a^2 + a*b := by
  sorry


example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  sorry


/- `ring` is a program that generates a Lean proof.
These proofs are checked by the *kernel* of Lean, which is the part of
Lean that can only check such low-level proofs.
This is the only part of Lean that needs to be bug-free
to ensure that Lean doesn't accept wrong proofs.
-/







/- ## rw -/

/- The `rw` tactic allows you to rewrite with equalities. -/

example (a b c d e : ℝ) (h : a = b + c) (h' : e = d - b) :
    a + e = d + c := by
  sorry


/- You can use `rw ... at h` to do the rewrite steps in a hypothesis. -/

example (a b c d : ℝ) (h : a = b + c) (h' : b = 0) :
    a + d = d + c + b := by
  sorry



/- You can use `rw ... at h` to do the rewrite steps in a hypothesis. -/

example (a b c : ℝ) (h : a + 1 = b) (h' : a + b = c) :
    c * 2 = a * 4 + 2 := by
  sorry



/- Instead of `ring`, we can also rewrite with lemmas manually. -/

#check add_zero a
#check zero_add a
#check add_comm a b








/- ## calc

If you write a sequence of rewrites, it is more natural and readable
to write your proofs as a calculation.
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by sorry
    _ = b*a - a*b := by sorry
    _ = 0         := by sorry



/-
Let's write a calc-proof by hand.
-/

example (a b c : ℝ) (h : a = b + c) : a * a = a * b + a * c := by
  sorry




/-
**Exercises**: Now try to prove these equalities with `calc`.
If you have time left, also try them directly with `rw`.
-/

example (a b c : ℝ) (h : a = b - c) (h2 : b * b = 2 * c) :
    a * b = (2 - b) * c := by
    calc
    a * b = (b-c) * b := by rw[h]
    _     = b * b - c * b := by ring
    _     = 2 * c - c * b := by rw[h2]
    _     = (2 - b) * c := by ring


example (x y z w : ℂ) (h : z = x * y) (h2 : y + 1 = w) :
    x * z = x ^ 2 * (w - 1) := by
  sorry

/-
If you haven't installed Lean yet, navigate to
  https://live.lean-lang.org/
and copy the following lines into the editor: (without the backticks)
```
import Mathlib.Tactic

example (a b c : ℝ) (h : a = b - c) (h2 : b * b = 2 * c) :
    a * b = (2 - b) * c := by
  sorry

example (x y z w : ℂ) (h : z = x * y) (h2 : y + 1 = w) :
    x * z = x ^ 2 * (w - 1) := by
  sorry
```
-/







/- ## Implication -/

/-
Besides computations, let's do logical reasoning with Lean.
We will introduce the *logical connectives*
to do more interesting reasoning than just calculations.

We will start with *Implication*.
"p implies q" is written in Lean as `p → q`.
-/

/-
**Forwards Reasoning** is reasoning forwards from the hypotheses
that other facts must hold.
We can do this with the `have` tactic.
`intro` is used to introduce assumptions.
`exact` or `assumption` can be used to finish the proof.
-/

example (p q r : Prop) (hpq : p → q) (hpqr : p → q → r) : p → r := by
  sorry

/- We can also use `specialize` to apply a hypothesis to arguments. -/
example (p q : Prop) (a b c : ℝ) (hq : p → q) (hr : p → q → a = b) :
    p → a + c = b + c := by
  sorry







/-
**Backwards reasoning** is where we chain implications backwards,
deducing what we want to prove from a combination of other statements
(potentially even stronger ones).
We do this with the `apply` tactic.
-/

example (p q r s : Prop) (hq : p → s → q) (hr : q → r) : s → p → r := by
  sorry

/- We can also use `exact` or `refine` with more complicated proof terms. -/

example (p q r : Prop) (hq : p → p → q) (hr : q → r) : p → r := by
  sorry




/- Often we can `apply` lemmas from Mathlib. -/
variable (f g : ℝ → ℝ)
#check (Continuous.add : Continuous f → Continuous g →
  Continuous (fun x : ℝ ↦ f x + g x))
#check (Continuous.mul : Continuous f → Continuous g →
  Continuous (fun x : ℝ ↦ f x * g x))
#check (continuous_id : Continuous (fun x : ℝ ↦ x))
#check (continuous_sin : Continuous (fun x : ℝ ↦ sin x))

example : Continuous (fun x ↦ x + x * Real.sin x) := by
  sorry

/-
**Difference between `rw` and `apply`**
- `rw` can be used to rewrite a subexpression (almost) anywhere in the goal,
  `apply` has to match the outermost thing you are trying to prove.
- *generally* you use `rw` with an equality,
  and `apply` with implications and "for all" statements.
-/




/- ## If and only if
* You can use `constructor` to prove an "if and only if" statement
* To use an "if and only if" statement `h`, you can use any of the following
  - `apply h.1`
  - `apply h.2`
  - `rw [h]`
  - `rw [← h]`
-/


#check exp_le_exp
#check (exp_le_exp.1 : exp a ≤ exp b → a ≤ b)
#check (exp_le_exp.2 : a ≤ b → exp a ≤ exp b)




example (h : a ≤ b) : exp a ≤ exp b := by
  sorry

example (h : a ≤ b) : exp a ≤ exp b := by
  sorry

example (h : exp a ≤ exp b) : a ≤ b := by
  sorry

example (h : exp a ≤ exp b) : a ≤ b := by
  sorry

example {p q : Prop} (h1 : p → q) (h2 : q → p) : p ↔ q := by
  sorry




/- ## Universal quantification

The tactics for universal quantification and implication are the same.
* We can use `intro` to prove an universal quantification (or implication).
* We can use `apply` or `specialize` to use a hypothesis
  that is a universal quantification (or implication). -/


def Injective (f : ℝ → ℝ) : Prop := ∀ x y : ℝ, f x = f y → x = y


example (f g : ℝ → ℝ) (hg : Injective g) (hf : Injective f) :
    Injective (g ∘ f) := by
  sorry





/- ## Conjunction

In Lean the conjunction of two statements `P` and `Q` is denoted by `P ∧ Q`,
read as "P and Q".

We can use a conjunction as follows:
* If `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`.
* To prove `P ∧ Q` use the `constructor` tactic.
Note that this is the same as for `↔`.

Furthermore, we can decompose conjunction and equivalences.
* If `h : P ∧ Q`, the tactic `obtain ⟨hP, hQ⟩ := h`
  gives two new assumptions `hP : P` and `hQ : Q`.
* If `h : P ↔ Q`, the tactic `obtain ⟨hPQ, hQP⟩ := h`
  gives two new assumptions `hPQ : P → Q` and `hQP : Q → P`.
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  sorry
