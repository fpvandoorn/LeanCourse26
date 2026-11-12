module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic


open Real (exp exp_pos log log_le_log)
open Function
public section
variable (a b c : ℝ)

#click_suggestions

/-
# Practical Remarks

* *Project 1* first PR due next Wednesday, 18.11
* run `lake exe cache get` in your formal conjectures folder if it's building
* *Project II* topic must be approved by next Wednesday

# Last time

* *Structures* define types containing both data and properties
* *Classes* are a useful general framework for associating extra
  'canonical' structure and overloading notation.
-/

structure PosPoint where
  x : ℝ
  y : ℝ
  z : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

#check PosPoint

variable (p : PosPoint)

#check (p.x : ℝ)
#check (p.y : ℝ)
#check (p.z : ℝ)
#check (p.x_pos : 0 < p.x)
#check (p.y_pos : 0 < p.y)
#check (p.z_pos : 0 < p.z)

#check (PosPoint.mk : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → PosPoint)

#synth TopologicalSpace ℝ
#synth AddCommGroup (ℝ × ℝ)

/-
# Today: universes, equivalence relations/quotients, choice

# Additive vs. multiplicative classes
In Mathlib, there are two notions of abelian groups,
one written using `(*, 1, ⁻¹)` and one using `(+, 0, -)`.
-/

#check CommGroup
#check AddCommGroup


/-
To explain this distinction, consider monoids
(sets/types with a binary operation and a unit for the operation).
`(ℝ, +, 0)` and `(ℝ, *, 1)` are both monoids,
and we want to have a distinction in notation and
lemma names of these two structures.
-/

#check Monoid
#check AddMonoid

#synth Monoid ℝ
#synth AddMonoid ℝ

example (x : ℝ) : x + 0 = x := by rw [add_zero x]
example (x : ℝ) : x * 1 = x := by rw [mul_one x]

/-
In Mathlib there is a `@[to_additive]` command
that automatically translates a lemma written
multiplicatively to a lemma written additively.
-/

@[to_additive]
lemma mul_assoc₄ {M : Type*} [Monoid M] (a b c d : M) : a * b * c * d = a * (b * (c * d)) := by
  simp [mul_assoc]

#check mul_assoc₄
#check add_assoc₄

/- # A note on universes


Lean has a hierarchy of universes. -/


--#check (ℝ : Type 1)
--#check ULift.{1,0} ℝ
#check Type
#check Type → Type
#check Type 1
#check Type 2

/- You can also work in a variable universe. -/

universe u v
#check Type u
#check Type (v + 3 + 1)
#check Type (max u v)
#check fun (α : Type u) (β : Type v) ↦ α → β
--#check Type (u + v) -- the operations on niverses are very limited.

/-
* `Type*` means `Type u` for a *variable* `u`
* `Type _` means an arbitrary universe (variable or not)

In Mathlib, when introducing a new type `α`,
we generally write `(α : Type*)` to be as general as possible.
-/

#check Type*
#check Type _

#check Type 4 → Prop

example : Type (u + 3) = Type _ := by rfl
--example : Type (u + 3) = Type* := by rfl -- error

/-
* `Prop` is a bottom universe below `Type`.
* `Sort` is used to write "`Prop` or `Type`"
-/

#check Prop
#check Sort 0
example : Sort 0 = Prop := rfl
example : Sort 1 = Type := rfl
example (P : Prop) (p q : P) : p = q := rfl
#check Sort 1
#check Sort 2
#check Sort (u + 1)
#check Sort*


/-
* Many definitions are *universe polymorphic*
-/
#check List.{u}

/- ## A note on coercions

You can specify *coercions* to say that an element of one type
can be silently coerced to an element of another type.
We've already seen the coercions
`ℕ → ℤ → ℚ → ℝ → ℂ`
for numbers.
-/

#check fun n : ℕ ↦ (n : ℚ)

abbrev PosReal : Type := {x : ℝ // x > 0}

variable (x : PosReal)
#check x.val
#check x.property

instance : Coe PosReal Real where
  coe x := x.val

def diff (x y : PosReal) : ℝ := x - y

/- Exercise: explain why the following raises an error: -/
--def diff' (x y : PosReal) : ℝ := ↑(x - y)

/- coercions can be composed. -/
#check fun (x : PosReal) ↦ (x : ℂ)

/-
* We use `CoeSort` to coerce to `Type _` (or `Sort _`)
* We use `CoeFun` to coerce to functions.
-/
structure PointedType where
  carrier : Type*
  pt : carrier


instance : CoeSort PointedType Type* := ⟨fun α ↦ α.carrier⟩

-- variable (α : PointedType)
-- variable (a : α)

structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

variable {X Y : PointedType}

infix:50 " →.. " => PointedFunction

instance {X Y : PointedType} : CoeFun (X →.. Y) (fun _ ↦ X → Y) :=
  ⟨fun f => f.toFun⟩

-- This tells the pretty printer to print the operation with `↑`.
attribute [coe] PointedFunction.toFun

namespace PointedFunction

variable {X Y Z : PointedType}

@[simp] lemma coe_pt (f : X →.. Y) : f X.pt = Y.pt := f.toFun_pt

def comp (g : Y →.. Z) (f : X →.. Y) : X →.. Z where
  toFun := g ∘ f
  toFun_pt := by
    simp

end PointedFunction




/-
## A note on subtypes
-/

#check {x : ℝ // 2 ≤ x}

/- You can also treat a set `s` as the subtype `{x // x ∈ s}`.
This operation is a coercion. -/
section
variable (s : Set ℝ)
#check (s : Type)

example (s : Set ℝ) (x : s) : (x : ℝ) ∈ s := x.property

/- However, subtypes are often not that convenient to work with,
and generally it's easier to reformulate a statement without using subtypes. -/

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by
  intro x y hxy
  dsimp
  gcongr
  · exact (f x).property
  · apply hf
    exact hxy

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : Set.range f ⊆ {x | x > 0}) (h2f : Monotone f) :
    Monotone (log ∘ f) := by
  intro x y hxy
  dsimp
  gcongr
  · apply hf
    use x
  · apply h2f
    exact hxy

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by
  sorry


/- Define a function on the whole type, but
only specify that a function is well-behaved
on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by
  sorry

/- In Lean, many functions are defined using "junk values" outside their
domain. -/
#check Real.log

#eval 5 / 0
variable (x y : ℝ)
#check x / y


/-! # Equivalence relations -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the trivial equivalence relation on the integers. -/
def myEquivalenceRelation : Setoid ℤ where
  r k l := k = l
  iseqv :=
    { refl := by
        intro x
        rfl
      symm := by
        intros
        symm
        assumption
      trans := by
        intro x y z hxy hyz
        rw [hxy, hyz]
        }

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (k l : ℤ) :
  letI := myEquivalenceRelation; k ≈ l ↔ k = l := by rfl

/-
Let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/
def quotient_equiv_subtype :
    Quotient (myEquivalenceRelation) ≃ ℤ where
      toFun := Quotient.lift (fun a : ℤ => a)
        (by
          intros
          simp at *
          assumption)
      invFun a := Quotient.mk _ a
      left_inv := by
        unfold LeftInverse
        apply Quotient.ind
        intro a
        simp only [Quotient.lift_mk]
      right_inv := by
        intro a
        simp

/-- Let's define the equivalence relation for the even numbers: two numbers are equivalent
iff their difference is an even number. -/
def evensEquivalenceRelation : Setoid ℤ where
  r k l := ∃ n, k - l = 2 * n
  iseqv := {
    refl := by
      sorry
    symm := by
      sorry
    trans := by
      sorry
  }

/-
## Axiom of Choice

If time left, we will discuss how to use the axiom of choice.

This is one formulation of the axiom of choice in Lean.
-/

#check Classical.choose
#check Classical.choose_spec




/- This doesn't look like the axiom of choice,
since we're only choosing 1 element.
However, this is a *function* that takes a proof
of an existential and produces an element in `α` from it.
This is called *global choice* and it is a bit stronger
than the usual axiom of choice.
We can prove the usual axiom of choice from it.
-/

theorem normal_axiom_of_choice {ι α : Type*} {s : ι → Set α} (h : ∀ i, (s i).Nonempty) :
    Nonempty {f : ι → α | ∀ i, f i ∈ s i} := by
  let f i := (h i).choose
  use f
  intro i
  exact (h i).choose_spec


-- END OF LECTURE

/- When working with choice,
opening the namespace `Classical` is useful.
If Lean complains that it cannot synthesize `Decidable` or `DecidableEq`
then you should `open Classical`. -/
open Classical



/-
We will use the axiom of choice to define left/right inverses of a function.

Suppose we have a function `f : α → β`.
Can we find a inverse `g : β → α` of `f`?
Not without assuming that `f` is bijective...

But suppose we try, suppose that `∃ x, f x = y`, and we want to define `g y`.
It must be one of the `x` such that `f x = y`.
We can choose one such `x` using *the axiom of choice*.
-/

noncomputable section Inverse

variable {α β : Type*} (f : α → β)

def conditionalInverse (y : β) (h : ∃ x : α, f x = y) : α :=
  Classical.choose h

lemma invFun_spec (y : β) (h : ∃ x, f x = y) :
    f (conditionalInverse f y h) = y :=
  Classical.choose_spec h


/-
You can ask Lean whether a declaration depends on the axiom of choice.
The actual axiom of choice is stated a bit differently in Lean,
and `Classical.choose` is derived from that. -/

#print axioms conditionalInverse
#check Classical.choice
#print Nonempty

#check axiom_of_choice



/- We can now define the function by cases on whether it lies in the range of `f` or not. -/

variable [Inhabited α]
def inverse (f : α → β) (y : β) : α :=
  sorry

lemma inverse_spec (y : β) (h : ∃ x, f x = y) :
    f (inverse f y) = y := by
  sorry




/- We can now prove that `inverse f` is a right-inverse if `f` is surjective
and a left-inverse if `f` is injective.
We use the `ext` tactic to show that two functions are equal. -/

lemma rightInv_of_surjective (hf : Surjective f) : f ∘ inverse f = id := by
  sorry

lemma leftInv_of_injective (hf : Injective f) : inverse f ∘ f = id := by
  sorry

/- We can package this together in one statement. -/
lemma inv_of_bijective (hf : Bijective f) :
    ∃ g : β → α, f ∘ g = id ∧ g ∘ f = id := by
  sorry

end Inverse
