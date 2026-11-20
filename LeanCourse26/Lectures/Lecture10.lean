module

public import Mathlib.NumberTheory.LSeries.RiemannZeta

public noncomputable section
set_option linter.unusedVariables false

#click_suggestions

/-
## Practical remarks

* First PR for Project 1 due next Wednesday
* Make sure your conjecture isn't already in Formal Conjectures,
  including as an open pull request!
* Topic for Project 2 due next Wednesday

## Last time

* universes : necessary to avoid inconsistancies similar to Russell's paradox.
* coercions : the typeclasses `Coe`, `CoeSort` and `CoeFun`.
* equivalence relations and quotients
  `Quotient.mk`
  `Quotient.lift`
  `Quotient.sound`
  `Quotient.ind`
* The axiom of choice in Lean : `Classical.choose` and `Classical.choose_spec`
-/

#check Classical.choose

open Function in
example {α β : Type*} {f : α → β} (hf : Surjective f) :
    ∃ g : β → α, f ∘ g = id := by
  let g b := (hf b).choose
  use g
  ext b
  apply (hf b).choose_spec

/-
One remark on the axiom of choice:
The `obtain` tactic doesn't use the axiom of choice.
The type theory of Lean itself (without the axiom of choice)
only allows you to destruct the proof of an existential quantifier
when you're proving a proposition, not when you're constructing data
(an element of type that is not a proposition).
-/
example {α : Sort*} {p : α → Prop} (h : ∃ x, p x) : α := by
  --obtain ⟨x, hx⟩ := h -- this gives an error
  exact Classical.choose h

lemma test {α : Sort*} {p : α → Prop} (h : ∃ x, p x) : 1 ≤ 2 := by
  obtain ⟨x, hx⟩ := h -- this works fine
  exact one_le_two

#check Exists.elim

/-
## Comments on notation and namespaces

Recall that namespaces are a way to organize declarations
-/
#check Set.pi
#check Finset.pi
#check Real.pi

--#check pi
open Set in
#check pi

/- Some definitions are `protected`, meaning that their names
cannot be shortened -/

-- open Real in
-- #check pi

/- You can define custom notation with the `notation` keyword -/
notation "φ" => (1 + √5) / 2

lemma φ_sq : φ ^ 2 = φ + 1 := by
  simp [add_sq, div_pow]; ring

/- It is possible to limit where notation can be used.
* `local notation` only defines the notation within that section.
* `scoped notation` only defines the notation within that namespace. -/

namespace TestNotation

local notation a "⊹" b => a + b
scoped notation a "⋆" b => a * b

#eval 4 ⊹ 5
#eval 4 ⋆ 5

end TestNotation

section

-- #check 4 ⊹ 5
-- #check 4 ⋆ 5

open TestNotation in
#eval 4 ⋆ 5

--#check 4 ⊹ 5

end

/- Some notation patterns are common enough to have their
own commands, like `infix`, `prefix` and `postfix`.
You can specify the *precedence* of the notation to establish
an order of operations.
Multiplication has higher precedence (70) than addition (65).
-/

section CustomNotation

local infix:65 " ⊹ " => Nat.add
#eval 3 ⊹ (5 * 2)
#eval (3 ⊹ 5) * 2
#eval 3 ⊹ 5 * 2
#eval 3 ⊹ 5 * 2 = 13 -- equality has a precedence of 50

/- Exercise: find and correct the error in the following:
-/

local postfix:75 "!" => Nat.factorial
example : 1 + 3! = 7 := by rfl


/- Notation can be overloaded. You can give notation priorities
to help Lean decide which meaning to use.
`(priority := high)` -/
#check ℤ ⊕ ℕ

local infix:65 " ⊕ " => Nat.add
#check 2 ⊕ 3
#check ℤ ⊕ ℕ

end CustomNotation

/- If you want to define more complicated notations,
look at how a similar notation is already defined. -/
variable {s : ℕ → Set ℝ}
#check ⋃ i, s i



/-
## Finiteness

We saw `Finset` briefly when discussing the `∑`-notation.

A `Finset` is a finite set where Lean can exactly
compute what elements it contains.
-/

open Finset

#check ({1, 2, 3} : Finset ℕ)
#eval 1 ∈ ({1, 2, 3} : Finset ℕ)

#eval ∑ i ∈ {1, 2, 3}, i ^ 2

#check ({j ∈ {1, 2, 3, 4} | Even j} : Finset ℕ)
#eval ({j ∈ {1, 2, 3, 4} | Even j} : Finset ℕ)

#eval {j ∈ range 100 | Prime j}
#eval {j ∈ range 100 | #j.primeFactors > 2}

--#check ({j ∈ {1} | RiemannHypothesis } : Finset ℕ)



/-
The reason that `Even j` does work is because Lean knows that
`Even` is "decidable": there is an algorithm to decide
whether a number is even or not.
-/
#check Decidable

#synth DecidablePred (Even : ℕ → Prop)
--#synth Decidable RiemannHypothesis


/-
If you open the `Classical` namespace, then you can treat
any finite set as a `Finset`.
-/

open Classical in
def riemannHypothesisSet : Finset ℕ := {j ∈ {1} | RiemannHypothesis }

open Classical in
#check ∑ i ∈ riemannHypothesisSet, i

open Classical in
#synth Decidable RiemannHypothesis

#check Classical.propDecidable


/- We have the usual operations on `Finset`, similar to `Set`. -/

section Nat

variable (s t : Finset ℕ)

#check s ∩ t
#check s ∪ t
#check s \ t
#check (∅ : Finset ℕ)

example {a b c : Finset ℕ} : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x
  simp
  tauto


end Nat

/-
If we work in an arbitrary type, to do operations on `Finset`,
we need to to be able to decide/compute whether two elements are equal.

For example, it's not easy to decide whether `riemannHypothesisSet` equals `{1}`
-/

section DecidableEq

variable {α : Type*} (s t : Finset α)
variable [DecidableEq α]

--open Classical
#check s ∪ t

end DecidableEq

/- You can take the maximum of a Finset by using `Finset.max'`,
but we have to prove that the finite set is non-empty.

Alternatively, we can use `Finset.max`, but that returns an element of `WithBot α` -/

#check Finset.min'

example : Finset.min' {0, 5, 10} ⟨0, by decide⟩ = 0 := by rfl

example : Finset.min (range 10) = 0 := by rfl
example : Finset.min (∅ : Finset ℕ) = ⊤ := by rfl

example : ({1,2,3} : Finset ℕ) = {3,2,1} := by decide

/-
`insert a s` means inserting one new element to a `Finset`
(that also works for `Set`).
`{0, 1, 2}` is just notation for using `insert` a few times.
-/

example (s : Finset ℕ) (a : ℕ) : insert a s = {a} ∪ s := by rfl


set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)



/-
We can prove something for all finite sets by using
the following induction principle.
-/

#check Finset.induction


example {α : Type*} [DecidableEq α] (f : α → ℕ)
    (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction with
  | empty => rw [prod_empty]; decide
  | insert a s ha ih =>
    rw [prod_insert]
    · apply mul_ne_zero
      · apply h
        simp
      · apply ih
        intro x hx
        apply h
        -- simp
        -- right
        -- exact hx
        exact mem_insert_of_mem hx
    · assumption




/- We can write `#s` for the cardinality of a Finset. -/
example {α : Type*} (s : Finset α) : #s = ∑ i ∈ s, 1 := by simp



/- There are other notions of finiteness too.
* `Fintype α` is a typeclass which records a `Finset α` containing
  all elements of `α`, called `Finset.univ`. This is useful for computation.
* `Finite α` is a typeclass which asserts the existance of an equivalence
  to `Fin n` for some `n`.

We can use `Infinite` to say that a type is infinite.
-/

#synth Fintype (Fin 5)

example : Fintype.card (Fin 5) = 5 := by rfl

example {α : Type*} [Fintype α] (x : α) : x ∈ Finset.univ := mem_univ x

example : Infinite ℕ := by exact?

#check range 3
#check Fin 3


/-
We write `s.image f` for the image of the Finset `s`
under the function `f`.
Let's do a simple computation with cardinalities.
-/
example (m n : ℕ) (h : n ≤ m) :
    #(range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint]
  · rw [card_image_of_injOn, card_range, two_mul]
    simp
  · rw [disjoint_iff_ne]
    simp
    lia


/-
Let's do a computation using a double counting argument:
If `G` is a bipartite graph with independent sets `s` and `t`.
Suppose that the degree of all vertices in `s` is at least 3,
and the degree of all vertices in `t` at most 1.

Then `3 * #s ≤ #t`.
-/

open Classical in
example {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #s ≤ #t := by
  calc
    3 * #s = ∑ a ∈ s, 3 := by simp [mul_comm]
         _ ≤ ∑ a ∈ s, #{b ∈ t | r a b} := by gcongr; apply h_left; assumption
         _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
         _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := by exact sum_comm
         _ = ∑ b ∈ t, #{a ∈ s | r a b} := by simp
         _ ≤ ∑ b ∈ t, 1 := by gcongr; apply h_right; assumption
         _ = #t := by simp


/-
## Inductive types

Lean's rules allow us to define *inductive types*.
An inductive type is a type with recursive constructors.

For example, the following is a declaration of (a copy of) the natural numbers.
every element is either `zero` or `succ` of an (already constructed) natural number.
-/

inductive NaturalNumber where
  | zero : NaturalNumber
  | succ (n : NaturalNumber) : NaturalNumber

#check NaturalNumber.zero

open NaturalNumber
#check succ (succ (succ zero))



/-
Similarly, a list of elements from `α` is inductively defined by saying that:
- the empty list is a list
- if you have a list `l` and an element `x` in `α`,
  then adding `x` in front of `l` gives a new list.
-/

inductive MyList (α : Type*) where
  | nil : MyList α
  | cons : α → MyList α → MyList α



/- We'll use the `List` that Lean already knows,
since it comes with nice notation. -/
#check ([] : List ℕ)
#check List.cons 5 (List.cons 3 List.nil)
#check 5 :: 3 :: []
#check [1, 2, 3, 4]
#eval [1, 2] ++ [3, 4]


/- Inductive types allow you to define new operations on it
by *pattern matching*.
This defines a new function that is defined by the given equations. -/

def myAdd : NaturalNumber → NaturalNumber → NaturalNumber
  | zero,   m => m
  | succ n, m => succ (myAdd n m)

@[simp]
def rev {α : Type*} : List α → List α
  | List.nil => []
  | List.cons a as => rev as ++ [a]

#eval rev [1,2,3]

/- We can prove properties about inductive types using `induction`. -/

lemma rev_append {α : Type} {as bs : List α} : rev (as ++ bs) = rev bs ++ rev as := by
  induction as with
  | nil => simp
  | cons head tail ih =>
    simp [ih]

-- End of lecture

/- Exercise : prove the following -/
lemma rev_rev {α : Type} (as : List α) : rev (rev as) = as := by
  sorry
