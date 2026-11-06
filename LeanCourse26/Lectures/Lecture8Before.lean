module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real
public section
variable (a b c : ℝ)

#click_suggestions

/-
# Last time

* Git, project descriptions.

* recursive functions can be defined by *pattern-matching*.
  Such a function must be terminating.
* proofs by induction: `induction` tactic
  - `induction n generalizing m with` generalizes the
    inductive hypothesis,
  - `induction ... using ... with` allows using other induction
    principles (e.g., strong induction or two-step induction)
-/


/-
# Today: Structures and classes

Structures are used to build data and properties together.
For example in the structure below `Point` bundles three coordinates
together.
`x`, `y` and `z` are called *fields* of the structure `Point`.
-/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ


#check Point

section
/- Given a point, we get access to its coordinates / projections. -/

variable (a : Point)
#check a.x
#check a.y
#check a.z
#check Point.x a

example : a.x = Point.x a := rfl

end





/- We can prove that two points are equal using the `ext` tactic. -/

example (a b : Point)
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  sorry

example (a b : Point)
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  sorry

#check Point.ext
#check Point.ext_iff

/-
There are multiple ways to define a point
(or more generally an instance of a structure).

Tip: if you write `:= _` for a Point, a lightbulb 💡 will appear.
Clicking it will give you the skeleton to write all fields.
-/

def myPoint1 : Point where
  x := 1
  y := 2
  z := 3

def myPoint2 :=
  { x := 1, y := 2, z := 3 : Point }

def myPoint3 : Point :=
 {
   x := 1
   y := 2
   z := 3
 }

def myPoint4 : Point := ⟨1, 2, 3⟩

def myPoint5 := Point.mk 1 2 3



namespace Point

/- We can define operations on points, like addition. -/

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

def add' : Point → Point → Point :=
  fun ⟨ux, uy, uz⟩ ⟨vx, vy, vz⟩ ↦ ⟨ux + vx, uy + vy, uz + vz⟩

def add'' : Point → Point → Point
  | ⟨ux, uy, uz⟩, ⟨vx, vy, vz⟩ => ⟨ux + vx, uy + vy, uz + vz⟩

/- We define these operations in `namespace Point`.
This means that if this namespace is open we can write `add p q`.
If the namespace isn't open, we have to write `Point.add p q`.

In either case, we can use the *projection notation*,
`p.add q` where `p q : Point`.
Lean knows that we mean the function `Point.add`,
by looking at the type of `p`, which is `Point`. -/

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

/- You can *open* a namespace to shorten the names in it. -/
open Point

#check add myPoint1 myPoint2











namespace Point

/-
We can prove properties about points. `protected` in the line below means that
even in the namespace `Point` we still have to write `Point.add_comm`
(the name is not shortened) -/

protected lemma add_comm (a b : Point) : add a b = add b a := by
  sorry

#check Point.add_comm

/- We can also state that we want to use the `+` notation here.
In that case, we have to write lemmas stating how `+` computes. -/

instance : Add Point := ⟨add⟩

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

example (a b : Point) : a + b = b + a := by
  sorry

end Point





/- We can bundle properties in structures -/

structure PosPoint where
  x : ℝ
  y : ℝ
  z : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

def PosPoint.add (a b : PosPoint) : PosPoint :=
{ x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z
  x_pos := by sorry
  y_pos := by sorry
  z_pos := sorry }








/-
Going from `Point` to `PosPoint` has code duplication.
We don't want this when defining monoids, groups, rings, fields.
-/

structure PosPoint' extends Point where
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z

#check PosPoint'.toPoint

def PosPoint'.add (a b : PosPoint') : PosPoint' where
  toPoint := a.toPoint + b.toPoint
  x_pos := by sorry
  y_pos := by sorry
  z_pos := by sorry








/-
We could also define a type like this using a subtype.
Its notation is very similar to sets, but written as `{x : α // p x}`
instead of `{x : α | p x}`.
-/

abbrev PosReal : Type :=
  { x : ℝ // x > 0 }

def setOfPositiveReals : Set ℝ :=
  { x : ℝ | x > 0 }


example (x : PosReal) : x.val > 0 := x.prop

example (x : PosReal) : x.1 > 0 := x.2


def PosPoint'' : Type :=
  { x : ℝ × (ℝ × ℝ) // x.1 > 0 ∧ x.2.1 > 0 ∧ x.2.2 > 0 }

/- `×` is notation for the cartesian product of two types -/
#check Prod


/-
Using subtypes doesn't give you nice projections names.
It gets ugly when you have more than 2 projections.
-/






/- Structures can have parameters (arguments) -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

#check Triple.mk 1 2 3

#check Triple.mk cos sin tan










/-
## Equiv

An important structure is equivalences between two types,
i.e. a bijection (with a chosen inverse).
This exists in the library as `Equiv α β` or `α ≃ β`.
-/

#check Equiv

example {α β : Type*} (e : α ≃ β) (x : α) : β := e.toFun x
example {α β : Type*} (e : α ≃ β) (x : α) : β := e x

example {α β : Type*} (e : α ≃ β) : β ≃ α := e.symm
example {α β : Type*} (e : α ≃ β) (y : β) : α := e.symm y



/-
As an exercise, try to prove the following equivalences.
Lean *might* be able to figure out `left_inv` and `right_inv` itself.
`Unit` has only 1 element, which can be denoted with `()`
`Bool` has two elements, `true` and `false`
-/

example : PosPoint ≃ PosReal × PosReal × PosReal := by
  sorry

example {α : Type*} : (Unit → α) ≃ (α → Unit) × α := by
  sorry

example {α : Type*} : (Bool → α) ≃ α × α := by
  sorry

/-
## Abelian groups
Let's define abelians group in Lean.
(This is not the way Mathlib does it.)
-/

structure AbelianGroup where
  G : Type*
  add (x y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg (x : G) : G
  add_neg : ∀ x : G, add x (neg x) = zero

def IntGroup : AbelianGroup where
  G := ℤ
  add a b := a + b
  comm := Int.add_comm
  assoc := Int.add_assoc
  zero := 0
  add_zero := Int.add_zero
  neg a := -a
  add_neg := Int.add_right_neg

lemma AbelianGroup.zero_add (g : AbelianGroup) (x : g.G) :
    g.add g.zero x = x := by
  sorry



/-
Issues with this approach:
* we want a notation for `AbelianGroup.add` and `AbelianGroup.neg`.
* we want this to be automatically attached to certain
  concrete type such as `ℕ`, `ℝ`, and not have to write `IntGroup`...
* we want that Lean knows that `G × G'` is an abelian group
  if `G` and `G'` are.

Using `class` instead of `structure` tells Lean to
create a database of "instances of this class".
The `instance` command allows to add entries to this database.

Instances are "keyed" by their parameters, so we make the type
a parameter instead of a field.
-/


class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

instance : AbelianGroup' ℤ where
  add := fun a b ↦ a + b
  comm := add_comm
  assoc := add_assoc
  zero := 0
  add_zero := by simp
  neg := fun a ↦ -a
  add_neg := by exact?

#eval AbelianGroup'.add (2 : ℤ) 5

/-
Let's locally declare some notation to work with our abelian groups.
The `:70` and `:max` are called *precedences* of the notation.
The higher, the more tightly the notations "binds" to its arguments.
-/

infixl:70 " +' " => AbelianGroup'.add

notation " 𝟘 " => AbelianGroup'.zero

prefix:max "-'" => AbelianGroup'.neg


#check 2 * 3 -- use "Go to Declaration" to see the precedence of *.

/-
When you assume you have an object in a certain class,
you put them in square brackets (and giving a name to them is optional).
Such arguments are called *instance-implicit* arguments,
Lean will provide them automatically by searching the database.

As an illustration
-/

#check AbelianGroup'.add

instance AbelianGroup'.prod (G G' : Type*)
    [AbelianGroup' G] [AbelianGroup' G'] : AbelianGroup' (G × G') where
  add a b := (a.1 +' b.1, a.2 +' b.2)
  comm a b := by sorry
  assoc a b c := by sorry
  zero := (𝟘, 𝟘)
  add_zero a := by sorry
  neg a := (-' a.1, -' a.2)
  add_neg a := by sorry


/-
Now Lean will figure out itself that `AbelianGroup' (ℤ × ℤ)`.

If you want to check whether some instance exists,
you can use `infer_instance` or `#synth`.
-/

example : AbelianGroup' (ℤ × ℤ) := by infer_instance

#synth AbelianGroup' (ℤ × ℤ)

#check -' ((2, 3) : ℤ × ℤ) +' (4, 5)
#eval -' ((2, 3) : ℤ × ℤ) +' (4, 5)

example (x y : ℤ × ℤ) : x +' y = y +' x := by rw [AbelianGroup'.comm]




/- ## Additive vs Multiplicative classes. -/

/-
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

#synth CommMonoid ℝ
#synth AddCommMonoid ℝ
example (x : ℝ) : x + 0 = x := by rw [add_zero x]
example (x : ℝ) : x * 1 = x := by rw [mul_one x]

/-
In Mathlib there is a `@[to_additive]` command
that automatically translates a lemma written
multiplicatively to a lemma written additively.
-/

#check add_zero
#check add_neg_cancel
