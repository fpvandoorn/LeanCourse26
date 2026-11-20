-- Name: <insert your name here>

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: **Wednesday**, 25.11.2025 at 16.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice -/

variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup

-- Prove that the trivial subgroup of the integers has index zero.
example : (⊥ : AddSubgroup ℤ).index = 0 := by
  sorry

/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
-- Note: `(ψ ∘ φ) ⁻¹' U = φ ⁻¹' (ψ ⁻¹' U)` is the **wrong** statement, this is an equality of sets!
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : sorry := by
  sorry


/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : sorry := by
  sorry

#click_suggestions

/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by
  sorry

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

def frobeniusMorphism (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] :
    R →+* R :=
  sorry

@[simp]
lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p :=
  sorry

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by
  sorry

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by
  sorry

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by
  sorry

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by
  sorry

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by
  sorry

end Frobenius

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: To define the inverse of a unit, you need to use `Exists.choose`. -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

lemma IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by
  sorry

noncomputable instance groupUnits : Group {x : R // IsAUnit x} :=
  sorry

-- you have the correct group structure if this is true by `rfl`
lemma aux (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by sorry

end Ring

-- Here's an example of using `rfl` inside rintro. This will be useful in the exercises below.
example { x y : ℝ} (h : x ≤ y) : ¬y ≤ x → x ≠ y := by
  contrapose!
  rintro ⟨rfl⟩
  assumption

/-! # Exercises to hand in -/

section conjugate

/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G :=
  sorry

-- Characterise normal subgroups in terms of your definition.
example {H : Subgroup G} : H.Normal ↔ sorry := by
  sorry

/- Prove the following lemmas. In the language of group action (next Tuesday), they prove that
a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  sorry

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by
  sorry

end conjugate

section finite

section

variable {G : AddSubgroup ℚ}

-- In this section, you will prove a nice group theory fact: `(ℚ, +)` has no non-trivial subgroup
-- of finite index: any finite index subgroup must be `⊤`. Follow the steps below.

-- In the proof we will consider the following subgroup, consisting of all `n`-fold multiples
-- of rational numbers.
def multiple (n : ℕ) : AddSubgroup ℚ :=
  sorry

-- If your definition above is correct, this proof is true by rfl.
lemma mem_multiple_iff (n : ℕ) (q : ℚ) : q ∈ multiple n ↔ ∃ r, n * r = q := by sorry

-- The next lemma is a general fact from group theory: use mathlib to find the right lemma.
-- Hint: it's similar to `Subgroup.pow_index_mem`.

-- One approach: do `#check Subgroup.pow_index_mem`, go to definition and find the additive version.
#check AddSubgroup.nsmul_index_mem

lemma step1 {n : ℕ} (hG : G.index = n) (q : ℚ) : n • q ∈ G := by
  sorry

lemma step2 {n : ℕ} (hG : G.index = n) : multiple n ≤ G := by
  sorry

lemma step3 {n : ℕ} (hn : n ≠ 0) : multiple n = ⊤ := by
  sorry

-- The goal of this exercise: (ℚ, +) has no non-trivial subgroups of finite index.
example (hG : G.index ≠ 0) : G = ⊤ := by
  sorry

end

section frobenius

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by
  have hp' : p.Prime := hp.out
  -- `Finset.Ioo a b` is the finite set `{n | a < n < b }`.
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p) := by
    sorry
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    sorry
  have : ∑ i ∈ Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
    calc
     _ =  ∑ i ∈ Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by
       sorry
     _ = 0 := by
       sorry
  sorry

end frobenius
