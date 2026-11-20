module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

open Function Set Ideal Polynomial
noncomputable section

/- ## Practical comments

* Project 1: check if your PR has gotten a review yet.

* Project 2: get your project topic approved if it hasn't been yet.
-/

#click_suggestions

/- ## Last time: group theory

- monoids and groups,
- group homomorphisms and isomorphisms,
- subgroups and normal subgroups,
- quotient groups
-/

section Commutator

variable (G : Type*) [Group G]

def Commutator : Subgroup G :=
  Subgroup.closure {g : G | ∃ x y : G, x * y * x⁻¹ * y⁻¹ = g}

open Subgroup in
local instance : Subgroup.Normal (Commutator G) :=
  sorry

abbrev Abelianization' := G ⧸ Commutator G

example : CommGroup (Abelianization' G) := by
  sorry


/- Recall that there is a hierarchy of algebraic instances:
`CommGroup` extends `Group` and `CommMonoid`,
`CommMonoid` extends `Monoid`, `CommSemiGroup`, etc
This can lead to some tricky error messages
-/
section InstanceWarning

variable [CommGroup G]

example (a b : G) : a * b = b * a := by
  --rw [mul_comm] -- two competing `Mul G` instances
  sorry


end InstanceWarning

end Commutator

/- # Index of a subgroup

The index of a subgroup `H` of a group `G` is the cardinality of
the space `G / H` of left cosets.
If this space is infinite, the index is `0`.
If `H` is a normal subgroup of finite index, this index is the
cardinality of the quotient group.
-/
section Index

variable {G : Type*} [Group G] (H : Subgroup G)

#check H.index
example : H.index = Nat.card (G ⧸ H) := rfl

-- The trivial subgroup in the integers has index 0, as ℤ is infinite.
#check (⊥ : AddSubgroup ℤ).index

-- If a subgroup has index two, it is normal.
example (hH : H.index = 2) : H.Normal := Subgroup.normal_of_index_eq_two hH



/- # Permutation groups

Given a type `α`, a *permutation* of `α` is a bijective map `α → α`.
The collection of all permutations of `α` forms a group
the **permutation group** on `α`.
-/
#check Equiv.Perm ℤ
#synth Group (Equiv.Perm ℤ)

open scoped Nat -- activate factorial notation

-- The permutation group on `n` symbols has `n!` elements.
example {n : ℕ} : Nat.card (Equiv.Perm (Fin n)) = (n)! := by
  sorry

-- Each permutation has a sign: the **alternating group** is the subgroup of all *even*
-- permutations, i.e. those with positive sign.
#check Equiv.Perm.sign

variable {α : Type*} [Fintype α] [DecidableEq α]

example : alternatingGroup α = Equiv.Perm.sign.ker := rfl

-- For n ≥ 5, the alternating group in n letters is simple: it has no non-trivial subgroups.
#check IsSimpleGroup
#check Subgroup.isSimpleGroup_iff

example : IsSimpleGroup (alternatingGroup (Fin 5)) := by
  sorry


/- ## Ring theory -/

/- # Rings

The type `Ring α` is the type of all ring structures on `α`.
It is implemented as a typeclass.
-/
#print Ring

/- Lean uses `Ring` and `CommRing` for rings and commutative rings. -/
example : CommRing ℤ := by infer_instance

/- Also important are *semirings*, which are rings without postulating negation. -/
example : CommSemiring ℕ := by infer_instance

/- A field (German: Körper) is a nontrivial commutative ring with inverses. -/
example : Field ℚ := by infer_instance

#print Field

/- Many classes only take a type as argument,
others are predicates that take another class as argument -/
#check Field
#check IsDomain
#check EuclideanDomain
#check UniqueFactorizationMonoid

#check IsField


/- In Mathlib, many lemmas about multiplication are stated in two ways:
* For Group-like structures
* For Ring-like structures (with an absorbing element 0).
-/

#check mul_div_cancel_right -- group-like
#check mul_div_cancel_right₀ -- ring-like

/- Use Loogle to find lemmas you want.

`MonoidWithZero` and `GroupWithZero` capture the
multiplicative structure of a ring or a field
-/

#loogle (?a * ?b) / ?b = ?a
#loogle _ * _ = 0 ↔ _
#check mul_lt_mul_left
-- #loogle ?a * _ < ?a * _ ↔ _

#check MonoidWithZero
#check GroupWithZero



/- Note that the tactics for computation in a
`Ring` and `CommRing` is `noncomm_ring` resp. `ring`.-/
example {R : Type*} [CommRing R] (x y : R) :
    (x - y)^2 = x^2 - 2*x*y + y^2 := by ring

example {R : Type*} [Semiring R] (x y : R) :
    (x + y)^2 = x^2 + x*y + y*x + y^2 := by noncomm_ring

/- The binomial theorem.
The natural number `Nat.choose n m` is coerced to an element of `R`
using `Nat.cast`. -/
example {R : Type*} [CommRing R] (x y : R) (n : ℕ) : (x + y) ^ n =
    ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * Nat.choose n m := by
  exact add_pow x y n


/- We have a predicate `IsUnit` stating
whether an element of the ring is a unit. -/
example {R : Type*} [CommRing R] (x : R) :
    IsUnit x ↔ ∃ y, x * y = 1 := isUnit_iff_exists_inv


/- We can write `Rˣ` for the units of a ring
(i.e. the elements with a multiplicative inverse). -/
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {R : Type*} [Ring R] : Group Rˣ := by infer_instance


/- We write ring homomorphisms with `→+*`. -/
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y ∧ f (x * y) = f x * f y ∧
    f 1 = 1 ∧ f 0 = 0 :=
  ⟨f.map_add x y, f.map_mul x y, f.map_one, f.map_zero⟩

section Homs

variable {R S : Type*} [Ring R] [Ring S]

#check R →* S -- `MonoidHom`
#check R →+ S -- `AddMonoidHom`
#check R →+* S -- `RingHom`

variable (f : R →+* S)
#check (f : R →+ S)

end Homs

section Subring

variable {R : Type*} [Ring R] (S : Subring R)

/- A subring is a subset of `R`
that is an additive subgroup and multiplicative submonoid.

As subgroups, subrings are bundled as a set with closure properties.
They are not so useful, since we cannot quotient a ring by a subring. -/
example : Ring S := by infer_instance
example : (S : Type _) = {r : R // r ∈ S} := rfl

end Subring


/- ## Ideals -/


section Ring
variable {R : Type*} [CommRing R] {I J : Ideal R}

/- Ideals are additive subgroups that are closed under arbitrary multiplication. -/
example {x y : R} (hy : y ∈ I) : x * y ∈ I :=
  I.mul_mem_left x hy

example {x y : R} (hx : x ∈ I) : x * y ∈ I :=
  I.mul_mem_right y hx

/- Exercise: use loogle to find closure under addition -/


/- There are various operations on ideals. -/
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ I ⊓ J := mul_le_inf

example : CompleteLattice (Ideal R) := by infer_instance
example : CommSemiring (Ideal R) := by infer_instance

#check (⊥ : Ideal R)
#check (⊤ : Ideal R)


/- We write `Ideal.span s` for the smallest ideal containing `s`.
In particular, `Ideal.span {a}` is the principal ideal generated by `a`. -/

/- Exercise: use `click_suggestions` to find relevant lemmas. -/
example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by
  sorry


example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by
  sorry


example (n m : ℤ) : span {n} * span {m} = span {n * m} := by
  sorry


/- We can quotient a ring by an ideal. -/

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

variable {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsPrime] in
#synth IsDomain (R ⧸ I)

example {R : Type*} [CommRing R] (I : Ideal R) [h : I.IsMaximal] :
    Field (R ⧸ I) :=
  Quotient.field I

#check Ideal.Quotient.lift
#check Ideal.Quotient.eq



/- The Chinese remainder theorem can be stated
for ideals in a commutative ring. -/

example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (f : ι → Ideal R) (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) :
    (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i := by
  exact quotientInfRingEquivPiQuotient f hf

/- Exercise: what is the type of `IsCoprime`? What's the subtlety? -/


/- From this we can easily get the traditional version for `ℤ/nℤ`. -/

example (n : ℕ) : Ring (ZMod n) := by infer_instance

example {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* ∀ i, ZMod (a i) :=
  by exact ZMod.prodEquivPi a ha



example {R : Type*} [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R] (I : Ideal R) :
    ∃ x : R, I = span {x} := by exact Submodule.IsPrincipal.principal I




/- # Algebras and polynomials -/


/- `Algebra R A` is the type of all `R`-algebra structures on `A`.
This is implemented as a typeclass.
-/

variable {A : Type*} [Semiring A] [Algebra R A]

#print Algebra

/- An (associative unital) *algebra*  `A` over a ring `R`
is a semiring `A` equipped with a ring homomorphism `R →+* A`
whose image commutes with every element of `A`. -/
example : R →+* A := algebraMap R A

example (r : R) (a : A) :
    algebraMap R A r * a = a * algebraMap R A r :=
  Algebra.commutes r a

/- We can also denote `algebraMap R A r * a`
using scalar multiplication as `r • a`. -/
example (r : R) (a : A) : r • a = algebraMap R A r * a := Algebra.smul_def r a




/- An important algebra is the polynomial ring `R[X]` or `Polynomial R`.
We can write `X` or `Polynomial.X` for the polynomial variable. -/

example : Algebra R R[X] := by infer_instance

example {R : Type*} [CommRing R] : R[X] := X

/- The variable `X` is hard-coded in the notation -/
--example {R : Type*} [CommRing R] : R[Y] := Y

example {R : Type*} [CommRing R] (r : R) : R[X] :=
  X - C r

/- `C` is registered as a ring homomorphism. -/
#check C

/- You can access coefficients using `Polynomial.coeff` -/
example {R : Type*} [CommRing R] (r : R) :
  (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] :
  (X^2 + 2*X + C 3 : R[X]).coeff 1 = 2 := by simp

/- Defining the degree of a polynomial leads to a choice:
what is the degree of the `0` polynomial? -/
#check natDegree (R := R)
#check degree (R := R)
example : natDegree (R := R) 0 = 0 := rfl

/- `WithBot ℕ` can be seen as `ℕ ∪ {-∞}`, except that `-∞` is denoted `⊥`. -/
example : degree (R := R) 0 = ⊥ := rfl

example [IsDomain R] (p q : R[X]) :
    degree (p * q) = degree p + degree q := by
  exact degree_mul

example [IsDomain R] (p q : R[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q := by
  exact natDegree_mul hp hq


#check degree_add_le
#check degree_X
#check degree_mul_le
#check le_degree_of_ne_zero

/- Exercise : try to prove the following using the above lemmas
about degree -/
example [Nontrivial R] (p : R) :
    degree (X ^ 3 + C p * X ^ 2 + 2 * X - 4) = 3 := by
  sorry


/- `compute_degree!` and `monicity!` can automate some proofs. -/

example [Nontrivial R] (p : R) :
    degree (X ^ 3 + C p * X ^ 2 + 2 * X - 4) = 3 := by
  compute_degree!

example [IsDomain R] (p : R) :
    natDegree (X ^ 3 + C p * X ^ 2 + 2 * X - 4) = 3 := by
  compute_degree!

example [IsDomain R] (p : R) :
    Monic (X ^ 3 + C p * X ^ 2 + 2 * X - 4) := by
  monicity!



/- We can evaluate polynomials using `Polynomial.eval`. -/

example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := P.eval x

example {R : Type*} [CommRing R] (P : R[X]) (x : R) : R := eval x P

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

/- If `P : R[X]`, then we often want to evaluate `P` in algebras over `R`.
E.g. we want to say that `X ^ 2 - 2 : ℤ[X]` has a root in `ℝ` -/
#check aeval (R := R) (A := A)

example : ∃ (x : ℝ), aeval x (X ^ 2 - 2 : ℤ[X]) = 0 := by
  sorry

end Ring
