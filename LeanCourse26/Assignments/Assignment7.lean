-- Name: <insert your name here>

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Order.CompletePartialOrder

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace

#click_suggestions

/-! # Exercises to practice. -/

-- Work out the details in the definition of the principal filter.
def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by
    sorry
  sets_of_superset := by
    sorry
  inter_sets := by
    sorry

-- Work out the details in the definition of the atTop filter.
example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      sorry
    sets_of_superset := by
      sorry
    inter_sets := by
      sorry
  }

-- Harder: show the same result, over any pre-order. You may have to adjust your proof
-- of the intersection property.
example {α : Type*} [Nonempty α] [SemilatticeSup α] : Filter α :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      sorry
    sets_of_superset := by
      sorry
    inter_sets := by
      sorry
  }



/- You can use `filter_upwards` to conveniently conclude `Eventually` statements from `Eventually`
in one or more hypotheses using the same filter. -/
example {ι : Type*} {L : Filter ι} {f g : ι → ℝ} (h1 : ∀ᶠ i in L, f i ≤ g i)
    (h2 : ∀ᶠ i in L, g i ≤ f i) : ∀ᶠ i in L, f i = g i := by
  filter_upwards [h1, h2] with i h1 h2
  exact le_antisymm h1 h2

example {ι : Type*} {L : Filter ι} {a b : ι → ℤ} (h1 : ∀ᶠ i in L, a i ≤ b i + 1)
    (h2 : ∀ᶠ i in L, b i ≤ a i + 1) : ∀ᶠ i in L, |a i - b i| ≤ 1 := by
  sorry

/- The goal of the following exercise is to prove that
the regular open sets in a topological space form a complete lattice.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

instance : PartialOrder (RegularOpens X) := PartialOrder.ofSetLike _

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course Mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X where
  carrier := closure U
  isClosed' := by
    sorry

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X where
  carrier := interior C
  isOpen := by
    sorry
  regular' := by
    sorry

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by
  sorry

@[simp] lemma cl_int : U.cl.int = U := by
  sorry

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi






/-! # Exercises to hand in. -/

section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by
  sorry

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G :=
  sorry

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's prove the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/



def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x :=
  sorry


end GroupActions

section LinearAlgebra

variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]

/- Let's prove that a finite dimensional integral domain is a field.

This is already in mathlib, but let's prove it "by hand".
You may use `LinearMap.injective_iff_surjective` from mathlib,
but no other lemmas from Linear Algebra.

Hint: to prove a nonzero `a` has an inverse, define an auxilliary
linear map using a `let` statement.
-/
example [IsDomain R] [FiniteDimensional K R] : IsField R where
  exists_pair_ne := by
    sorry
  mul_comm := by
    sorry
  mul_inv_cancel := by
    sorry

end LinearAlgebra

section tendsto

/- Let's convince ourselves that convergence of a sequence and continuity at `x` as
defined in the lecture (and mathlib) correspond to the definitions we used in an analysis course. -/

/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

-- The following lemmas will be very helpful.
#check mem_nhds_iff
#check IsOpen.exists_Ioo_subset


lemma _root_.IsOpen.exists_Ioo_subset' {s : Set ℝ} {x : ℝ} (hs : IsOpen s) (hx : x ∈ s) :
    ∃ a b, a < b ∧ x ∈ Ioo a b ∧ Ioo a b ⊆ s := by
  sorry

example (u : ℕ → ℝ) (x : ℝ) : MyTendsto u atTop (𝓝 x) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x| < ε := by
  sorry



end tendsto
