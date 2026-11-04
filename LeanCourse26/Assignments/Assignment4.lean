-- Name: <insert your name here>

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Function Set

#click_suggestions

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean:
  Read chapters 5.2 and 5.4 for more on induction.
  Read chapter 7 for more on structures.
  Chapter 8 explains some of the design decisions for classes in Mathlib.

* Hand in the solutions to the exercises below. Deadline: **Wednesday**, 11.11.2025 at 16.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/


section casts

/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by
  sorry

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by
  sorry

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by
  sorry

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by
  sorry

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by
  sorry

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by
  sorry

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by
  sorry

end casts

section induction

/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i ∈ Finset.range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by
  sorry

example (n : ℕ) : ∑ i ∈ Finset.range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by
  sorry

example (n : ℕ) : 6 * ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  sorry

end induction

section structures

-- Recall the definition of points from the lecture.
@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

instance : Add Point := ⟨add⟩

@[simp] lemma add_x (a b : Point) : (a + b).x = a.x + b.x := by rfl
@[simp] lemma add_y (a b : Point) : (a + b).y = a.y + b.y := by rfl
@[simp] lemma add_z (a b : Point) : (a + b).z = a.z + b.z := by rfl

-- Prove that addition of points is associative.
lemma add_assoc {a b c : Point} : a + b + c = a + (b + c) := by
  sorry

-- Define scalar multiplication of a point by a real number
-- in the way you know from Euclidean geometry.
def smul (r : ℝ) (a : Point) : Point :=
  sorry

-- This registers the above operation as "scalar multiplication":
-- you can now write • for scalar multiplication.
instance : SMul ℝ Point := ⟨smul⟩

-- If you made the right definition, proving these lemmas should be easy.
@[simp] lemma smul_x (r : ℝ) (a : Point) : (r • a).x = r * a.x := by sorry
@[simp] lemma smul_y (r : ℝ) (a : Point) : (r • a).y = r * a.y := by sorry
@[simp] lemma smul_z (r : ℝ) (a : Point) : (r • a).z = r * a.z := by sorry

variable (x : ℝ) (a : Point)
#check x • a

end Point

-- This is the standard two-simplex in ℝ³. How does it look like, geometrically?
structure StandardTwoSimplex where
  coords : Point
  x_nonneg : 0 ≤ coords.x
  y_nonneg : 0 ≤ coords.y
  z_nonneg : 0 ≤ coords.z
  sum_eq : coords.x + coords.y + coords.z = 1

namespace StandardTwoSimplex

noncomputable section

-- Prove that a convex combination of two points in the standard simplex is again in the
-- standard simplex.
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
  (a b : StandardTwoSimplex) : StandardTwoSimplex
where
  coords := lambda • a.coords + (1 - lambda) • b.coords
  x_nonneg := by
    sorry
  y_nonneg :=
    sorry
  z_nonneg :=
    sorry
  sum_eq := by
    sorry
end

end StandardTwoSimplex

end structures


/-! # Exercises to hand-in. -/

section

-- In class, we saw that Lean does not accept definitions like this:
-- def wrong : ℕ → ℕ
--  | n => 1 + wrong (n + 1)

-- In this case, you can actually derive a contradiction from a function with this property.
-- Do so in the following exercise.
lemma contradictory_definition (f : ℕ → ℕ) (h : ∀ n : ℕ, f n = 1 + f (n + 1)) : False := by
  sorry


-- Hint for the exercise `contradictory_definition`:
-- use the hypothesis to study `f 0`: can you relate it to `f 1`, `f 2`, etc.?
-- Perhaps you can formulate a hypothesis and prove it by induction.


/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ 3) = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 := by
  sorry

end

section

-- Let's define a new operation on points in ℝ⁴.

@[ext]
structure Point4 where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ
-- x : 1, y : i, z : j, w : k

def op (a b : Point4) : Point4 where
  x := a.x * b.x - a.y * b.y - a.z * b.z - a.w * b.w
  y := a.x * b.y + a.y * b.x + a.z * b.w - a.w * b.z
  z := a.x * b.z - a.y * b.w + a.z * b.x + a.w * b.y
  w := a.x * b.w + a.y * b.z - a.z * b.y + a.w * b.x

-- Prove that op is associative.
lemma op_assoc {a b c : Point4} : op (op a b) c = op a (op b c) := by
  sorry

-- Investigate whether op is commutative: prove one of the following.
lemma op_comm : ∀ a b : Point4, op a b = op b a := by
  sorry

lemma not_op_comm : ¬(∀ a b : Point4, op a b = op b a) := by
  sorry


-- For the latter, you may the following helpful.
example : ⟨0, 1, 2, 3⟩ ≠ (⟨0, 3, 2, 3⟩ : Point4) := by
  sorry

example {x y : ℝ} (h : x ≠ y) : ⟨0, 1, x, 3⟩ ≠ (⟨0, 1, y, 3⟩ : Point4) := by
  sorry

-- If you want to use one of these lemmas, prove it also.
lemma ne_of_ne_x {a b : Point4} (h : a.x ≠ b.x) : a ≠ b := by
  sorry
lemma ne_of_ne_y {a b : Point4} (h : a.y ≠ b.y) : a ≠ b := by
  sorry
lemma ne_of_ne_z {a b : Point4} (h : a.z ≠ b.z) : a ≠ b := by
  sorry
lemma ne_of_ne_w {a b : Point4} (h : a.w ≠ b.w) : a ≠ b := by
  sorry


section Bipointed

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here


-- state and prove the lemma here


end Bipointed
