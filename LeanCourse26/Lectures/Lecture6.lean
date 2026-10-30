module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.FieldTheory.Finite.Basic

noncomputable section

#click_suggestions


/- # Last time

Last time we saw:

* `ext` proves that two functions are equal if their values are equal.

* There are many way to find useful lemmas. Notably:
  - shift-click on the goal or hypotheses, or subterms thereof.
  - `apply?`: find all lemmas that apply to the current goal;
  - `#loogle <query>`: syntactic searches;
  - `#leansearch "<query>."`: natural language searches.

* Orders:
  - `order` proofs something directly from order-theoretic facts
  - `linarith` proves (in)equalities using linear combinations of hypotheses.
  - `gcongr` applies monotonicity of functions
  - `grw` can rewrite with relations other than `=` or `↔`

* There is a tactic cheatsheet
-/


/- # Today: Sets

In set theory you can make sets with arbitrary elements.
In Lean, all sets have to be sets of elements from a specific type.

If `s : Set α` then `s` is a set with elements from `α`.
-/

#check Set ℕ
#check Set ℝ

variable {α β ι : Type*} (x : α) (s t u : Set α)

/- We can talk about membership and (strict) subsets. -/

#check x ∈ s       -- \in or \mem
#check x ∉ s       -- \notin
#check s ⊆ t       -- \sub
#check s ⊂ t       -- \ssub


variable (y : β)

/- You are not allowed to ask if elements
from a different type are in a set. -/
-- #check y ∈ s


/- We have the common set-theoretic operations.
Note: it is important that `s` and `t`
are sets of elements from the *same* type. -/

#check s ∩ t       -- \inter or \cap
#check s ∪ t       -- \union or \cup
#check s \ t       -- the normal symbol `\` on your keyboard,
                   -- (use a space afterwards to not use the unicode-replacement)

#check sᶜ          -- \compl or \^c
#check (∅ : Set α) -- \empty
#check (Set.univ : Set α)

/-
If you *open* a namespace, you are able to use names in it
without the prefix.
-/

-- #check (univ : Set α)

open Set

#check (univ : Set α)






/-
Showing that `x` is an element of
`s ∩ t`, `s ∪ t` or `sᶜ` corresponds by definition
to conjunction, disjunction or negation.
-/

#check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
#check (mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
#check (mem_compl_iff s x : x ∈ sᶜ ↔ x ∉ s)
#check (mem_sdiff x : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t)

#check (mem_univ x : x ∈ univ)
#check (notMem_empty x : x ∉ ∅)



/-
There are various ways to prove the following lemmas:
* use lemma `mem_inter_iff`
* use `simp`
* directly apply `constructor`
* give a direct proof: `⟨xs, xt⟩`
-/
example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by
  rw [mem_inter_iff]
  constructor
  · assumption
  · assumption

example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by
  simp
  exact ⟨hxs, hxt⟩

example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by
  constructor <;> assumption


example (hx : x ∈ s \ t) : x ∈ (s ∪ t) ∩ (sᶜ ∪ tᶜ) := by
  simp
  constructor
  · left
    simp at hx
    exact hx.1
  · right
    exact hx.2







/-
`s ⊆ t` means that for every element `x` in `s`,
`x` is also an element in `t`.
-/
#check (subset_def : (s ⊆ t) = ∀ x ∈ s, x ∈ t)
/- in other words, it states: `s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t` -/

example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  -- rw [subset_def]
  intro x hx
  constructor
  · exact hx.1
  · left
    exact hx.2

/- You can also prove it at the level of sets,
without talking about elements. -/
example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  gcongr
  exact subset_union_of_subset_left (fun ⦃a⦄ a_1 ↦ a_1) u





/- ## Proving two sets are equal

You can prove that two sets are equal by applying `subset_antisymm`
or using the `ext` tactic.

`ext x` can prove that `s = t` if `x ∈ s ↔ x ∈ t` for a new variable `x`.
-/
#check (subset_antisymm : s ⊆ t → t ⊆ s → s = t)

example : s ∩ t = t ∩ s := by
  ext x
  simp
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · intro ⟨h1, h2⟩
    exact ⟨h2, h1⟩





/-
## Set-builder notation
We can define the set of elements in `t` satisfying `P` using
  `{ x : t | P x }`
There are also variants
  `{ x     | P x }`
  `{ x ∈ s | P x }`
-/

def evens : Set ℕ := {n : ℕ | Even n}
def odds : Set ℕ := {n : ℕ | Odd n}

example : evensᶜ = odds := by
  ext n
  simp [evens, odds]




/-
The basic set-theoretic operations
are defined using the set-builder notation.
-/
example : s ∩ t = {x | x ∈ s ∧ x ∈ t} := by rfl
example : s ∪ t = {x | x ∈ s ∨ x ∈ t} := by rfl
example : s \ t = {x | x ∈ s ∧ x ∉ t} := by rfl
example : sᶜ = {x | x ∉ s} := by rfl

example : (∅ : Set α) = {_x | False} := by rfl
example : (univ : Set α) = {_x | True} := by rfl

/- we can write the intersection and set difference
in an alternative way. -/
example : s ∩ t = {x ∈ s | x ∈ t} := by rfl
example : s \ t = {x ∈ s | x ∉ t} := by rfl

/-
## Other operations on sets
-/

/- We can take the power set of `s` using either
`powerset s` or `𝒫 s`.
`𝒫` is typed using `\powerset`. -/
example (s : Set α) : 𝒫 s = {t : Set α | t ⊆ s} := by rfl


/- Question: What is the type of `𝒫 s`? -/
#check 𝒫 s
#check 𝒫 (𝒫 s)





/-
We can take unions and intersections of families of sets
in three different ways:

* Given a family of sets `C : ι → Set α`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements of `ι`.
-/
example (C : ι → Set α) :
    ⋃ i : ι, C i = {x : α | ∃ i : ι, x ∈ C i} := by ext; simp

example (C : ι → Set α) :
    ⋂ i : ι, C i = {x : α | ∀ i : ι, x ∈ C i} := by ext; simp



/-
* Given a family of sets `C : ι → Set α` and `s : Set ι`
  we can take the union and intersection of `C i`
  as `i` ranges over all elements in `s`.
-/
example (s : Set ι) (C : ι → Set α) :
    ⋃ i ∈ s, C i = {x : α | ∃ i ∈ s, x ∈ C i} := by ext; simp

example (s : Set ι) (C : ι → Set α) :
    ⋂ i ∈ s, C i = {x : α | ∀ i ∈ s, x ∈ C i} := by ext; simp




/-
* Given a collection of sets `C : Set (Set α)`
  we can take the union and intersection of `c`
  for all `c ∈ C`
-/

example (𝓒 : Set (Set α)) :
    ⋃₀ 𝓒 = {x : α | ∃ s ∈ 𝓒, x ∈ s} := by ext; simp

example (𝓒 : Set (Set α)) :
    ⋂₀ 𝓒 = {x : α | ∀ s ∈ 𝓒, x ∈ s} := by ext; simp


example (C : ι → Set α) (s : Set α) :
    s ∩ (⋃ i, C i) = ⋃ i, (C i ∩ s) := by
  ext x
  simp
  rw [and_comm]




/- We can take images and preimages of sets.

`f ⁻¹' s` is the preimage of `s` under `f`.
`f '' s` is the image of `s` under `f`.

On paper, you would write `f(A)` or `f[A]` for the image
and `f⁻¹(B)` or `f⁻¹[B]` for the preimage.
This notation is hard to parse for Lean, since parentheses and ⁻¹
have so many different meanings in mathematics.
Therefore we use this funny notation.
-/

variable {α β ι : Type*} (x : α) (s t u : Set α) (a b c : ℝ)
open Set

example (f : α → β) (s : Set β) : f ⁻¹' s = { x : α | f x ∈ s } := by rfl

example (f : α → β) (s : Set α) : f '' s = { y : β | ∃ x ∈ s, f x = y } := by rfl


example {s : Set α} {t : Set β} {f : α → β} :
    f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  constructor
  · intro h x hx
    simp
    apply h
    use x
  · intro h y hy
    -- obtain ⟨x, hxs, hxy⟩ := hy
    -- subst y
    obtain ⟨x, hxs, rfl⟩ := hy
    have hxt : x ∈  f ⁻¹' t := h hxs
    simp at hxt
    exact hxt


/- We can do pointwise operations on sets (e.g. the Minkowski sum). -/

open Pointwise

example (s t : Set ℝ) :
    s + t = {x : ℝ | ∃ a ∈ s, ∃ b ∈ t, a + b = x } := by rfl

example (s : Set ℝ) : -s = {x : ℝ | -x ∈ s } := by rfl


/- We can write `{a, b, c, ...}` to write enumerated sets. -/

example : ({1, 3, 4} : Set ℝ) + {0, 3} = {1, 3, 4, 6, 7} := by
  ext x
  simp [mem_add]
  norm_num
  tauto




/- ## Intervals -/

/-
Lean has the following names for intervals:
("c" = closed, "o" = open, "i" = infinity)
Icc a b = [a, b]
Ico a b = [a, b)
Ioc a b = (a, b]
Ioo a b = (a, b)
Ici a   = [a, ∞)
Ioi a   = (a, ∞)
Iic b   = (-∞, b]
Iio b   = (-∞, b)
-/

example : Icc a b = {x | a ≤ x ∧ x ≤ b} := by rfl
example : Ico a b = {x | a ≤ x ∧ x < b} := by rfl
example : Ioc a b = {x | a < x ∧ x ≤ b} := by rfl
example : Ioo a b = {x | a < x ∧ x < b} := by rfl
example : Ici a   = {x | a ≤ x}         := by rfl
example : Ioi a   = {x | a < x}         := by rfl
example : Iic b   = {x | x ≤ b}         := by rfl
example : Iio b   = {x | x < b}         := by rfl

example : Icc a b ∩ Ici c = Icc (max a c) b := by
  ext x
  simp only [mem_inter_iff, mem_Icc, mem_Ici, sup_le_iff]
  tauto



/- # Numbers -/

/-
Some useful tactics when dealing with numbers:
* `norm_num`: compute equalities and inequalities involving explicit
  numbers, or simplifies expressions involving numbers..
* `lia`: can do linear integer arithmetic on `ℕ` and `ℤ`.
* `positivity`: can show that something is positive/nonnegative/nonzero
  by using that its subterms are positive/nonnegative/nonzero.
* `field_simp` can simplify divisions.
-/

example : 2 ^ 3 + 17 = 300 / 12 := by norm_num

example (x : ℝ) : x + 5 + 3 = x + 8 := by
  rw [add_assoc]
  norm_num

example (n m : ℤ) : 2 * n + 1 ≠ 2 * m := by lia

example (n m k : ℝ) (hn : 0 < n) (hm : 0 ≤ m) (hk : 0 < k) :
    0 < n * m + k  := by positivity

example (x y z w : ℝ) (hz : z ≠ 0) :
    (x + y * w) / z = x / z + w * (y / z) := by
  field_simp


/- **Warning**
Division and subtraction of natural numbers
again returns a natural number.
This is division rounded down and truncated subtraction.
-/

#check 12
#check (12 : ℤ)

#eval 12 / 3
#eval 13 / 3
#eval 14 / 3
#eval 15 / 3
#eval 7 - 6
#eval 7 - 7
#eval 7 - 8

/-
If you give context that you are talking about integers/rational
numbers, then Lean will take the operations there.
-/
#eval (7 : ℤ) - (8 : ℤ)
#eval (7 : ℤ) - 8
#eval 7 - (8 : ℤ)
variable (k : ℤ)
#check k - 3
#eval (14 : ℚ) / 4

#check (1.51 : ℚ)
#eval (1.51 : ℚ)






/- ## Coercions
When using subtraction and division, it is usually better to
do the calculation in the rationals or reals.

We write the type ascription like `(<expression> : ℚ)` to tell Lean
that the expression should be interpreted as a rational number.

If you give a natural number expression, and tell Lean that it
should be a rational number, Lean will automatically
insert *coercions*, or canonical inclusions, in the expression.
In the infoview (right half of your screen),
these coercions are denoted with `↑`.

Coercions are used widely, between many types.
-/

variable (n : ℕ)
#check (n : ℂ)
#check (n + 1 : ℚ)
#check ((n - 3) / 2 : ℝ)
#check (5 : ℂ)
#check ((5 : ℕ) : ℂ)

example : ((5 : ℕ) : ℂ) = (5 : ℂ) := by norm_num

/- If you want precise control where the coercion is inserted,
you can use `↑` or a double type ascription.
However, just writing `↑` without any type information often doesn't
give Lean enough information to know what you mean. -/

#check (n + 1 : ℚ)
#check (↑(n + 1) : ℚ)
#check ((n + 1 : ℕ) : ℚ)
#check ((n + 1 : ℤ) : ℚ)

#check ↑(n + 1)




/-
Some tactics that are useful when working with coercions:
* `norm_cast`: pull coercions out of an expression.
  E.g. turn `↑n * ↑m + ↑k` into `↑(n * m + k)`
* `push_cast`: push coercions into an expression.
  E.g. turn `↑(n * m + k)` into `↑n * ↑m + ↑k`

Note: Sometimes you need additional hypotheses to pull/push casts
out of/into `-` or `/`, since `↑n - ↑m = ↑(n - m)` and
`↑n / ↑m = ↑(n / m)` are not always true.
-/

example (n : ℕ) : ((n + 1 : ℤ) : ℚ) = n + 1 := by norm_cast

example (n m : ℕ) (h : m ∣ n) : (↑(n / m) : ℚ) = ↑n / ↑m := by norm_cast

example (n m : ℕ) (h : (n : ℚ) + 1 ≤ m) : (n : ℝ) + 1 ≤ m := by
  norm_cast at h
  norm_cast

example (n m : ℕ) (h : n = m * m + 2) :
    (n : ℝ) - 3 = (m + 1) * (m - 1) := by
  rw [h]
  -- norm_cast isn't nice here
  push_cast
  ring

-- END OF LECTURE HERE
