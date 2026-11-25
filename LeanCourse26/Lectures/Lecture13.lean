module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Trace

open Function Set Polynomial

attribute [-instance] instSMulOfMul
noncomputable section

#click_suggestions

/- ## Practical remarks

* For *Project 1*, incorporate requested changes from the review by
  Friday.
* For *Project 2*, some presentations are starting next week. The
  project does not need to be complete to give a presentation on it,
  you can still present on a WIP.

-/

/- ## Last time

- ring theory: rings, subrings, ideals; ring homomorphisms, Chinese remainder theorem
- algebras, polynomials and tactics for them

-/

/- ## Today: Group actions and Linear Algebra -/

/- ### Group actions-/

section GroupAction

/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

/-
The dot • (typed as `\smul` in VS Code) denotes scalar multiplication: a multiplicative action
assumes you have a "scalar multiplication" instance on your type.
(We will encounter this later today when talking about vector spaces and modules.)
-/

#check mul_smul
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact mul_smul g g' x
example (x : X) : (1 : G) • x = x := by exact MulAction.one_smul x

-- In your algebra course, you might have seen a different definition, of a group action as a
-- group homomorphism `G → S_X` to the permutation group on `X`: Lean knows this also.
#check MulAction.toPermHom

-- If you want to just want to know the permutation induced by one particular element, use `toPerm`.
#check MulAction.toPerm

-- There is also a typeclass for additive actions
#check AddAction


/- Let's give an example: there are at least three actions of any group on itself
(1) doing nothing: `g • x = x` for all g and x
(2) acting by multiplication: `g • x = g * x`
(3) acting by conjugation: `g • x = g * x * g⁻¹`

Exercise: use `#synth` to find which instance of `G` acting on itself
is already in mathlib. Then fill in the right hand side of the below
example.
-/

#synth MulAction G G

#check fun x ↦ x + 2
#check (· + · * 4)

example {g g' : G} : g • g' = g * g' := by rfl


-- We can define our own actions to override the default instance
local instance (priority := 1100) trivialAction : MulAction G G where
  smul g x := x
  mul_smul := by
    intro x y b
    -- rfl -- works too
    simp [(· • ·)] -- tell simp to unfold the smul notation
  one_smul := by
    intro b
    rfl

-- Note that Lean finds a different action now.
#synth MulAction G G

example {g x : G} : g • x = x := by
  rfl


-- Let's define the action of `G` on itself by conjugation.
local instance (priority := 1100) conjugationAction : MulAction G G where
  smul g x := g * x * g⁻¹
  mul_smul := by
    intro x y b
    simp [(· • ·)]
    group
  one_smul := by
    intros
    simp [(· • ·)]

#synth MulAction G G

-- Note: `MulAction` is a class, and we just defined three different instances of it.
-- Typeclass search will find these instances, but you shouldn't always expect it to find
-- the same one: if you want to consider e.g. "G with this particular action", this is not very
-- robust yet. (One more robust way is a type synonym, which we may mention towards the end of
-- the course.)

#synth Group G

def G' := G

--#synth Group G'

def TrivAction (α : Type*) := α

local instance (priority := 1100) trivialAction' : MulAction G (TrivAction G) where
  smul g x := x
  mul_smul := by
    intro x y b
    -- rfl -- works too
    simp [(· • ·)] -- tell simp to unfold the smul notation
  one_smul := by
    intro b
    rfl

-- Lean knows about the diagonal action of a group.
instance : MulAction G (X × X) := by infer_instance
example {g h k : G} : g • (h, k) = (g • h, g • k) := rfl


-- Let's tell it about the product action: if G acts on X, then G × G acts on X × X.
instance : MulAction (G × G) (X × X) where
  smul g x := ⟨g.1 • x.1, g.2 • x.2⟩
  mul_smul := by
    intro x y b
    ext <;>
    apply mul_smul
  one_smul := by
    intro x
    ext <;>
    apply one_smul

example {g h : G} {x y : X} : (g, h) • (x, y) = (g • x, h • y) := by rfl


end GroupAction


section LinearAlgebra

/- # Modules and vector spaces

Most results in linear algebra are not formulated in terms of vector spaces,
but instead they are generalized to modules over a (semi)ring.
To state that `V` is a vector space over `K`, we actually use the word `Module`.
Note that we have to separately state that `(V, +)` is a group.
Scalar multiplication is written with `•` (\smul). -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


example (k : K) (v : V) : -k • v = k • -v := by
  rw [neg_smul, smul_neg]

#print AddCommGroup

/- Beware: every group also has a scalar multiplication w.r.t.
`ℕ` and `ℤ`, and the following lemmas relate this to the
scalar multiplication of `K`. -/

example (v : V) : (2 : K) • v = (2 : ℕ) • v := by
  exact ofNat_smul_eq_nsmul K 2 v
  --norm_cast

example (v : V) : (2 : ℤ) • v = (2 : K) • v := by
  norm_cast


/- A module `M` over a ring `R` is an abelian group `(M, +)`
together with a scalar multiplication `R → M → M`
with appropriate associativity and distributivity laws. -/

#print Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (r : R) (x y : M) : r • (x + y) = r • x + r • y := by exact smul_add r x y
example (r s : R) (x : M) : (r + s) • x = r • x + s • x := by exact add_smul r s x
example (r s : R) (x : M) : (r * s) • x = r • s • x := by exact mul_smul r s x
example (x : M) : (0 : R) • x = 0 := by exact zero_smul R x
example (x : M) : (1 : R) • x = x := by exact one_smul R x
example (r : R) : r • (0 : M) = 0 := by exact smul_zero r

/- As usual, we have submodules and quotients
Note that the quotient symbol is *not* the usual forward slash! -/
example (S : Submodule R M) : Module R (M ⧸ S) := by infer_instance


/- We have linear maps `M →ₗ[R] N` between modules.
We have to write `R` explicitly in this notation.



For example, in complex analysis there is an important difference
between `ℝ`-linear maps and `ℂ`-linear maps -/

variable {M' : Type*} [AddCommGroup M'] [Module R M']

#check M →ₗ[R] M'

/- We can take the product of modules-/
variable {N N' : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

#synth Module R (N × N')


/- `N × N'` is a biproduct: it is both the
product and coproduct of the modules `N` and `N'`. -/
example (f : M →ₗ[R] N) (g : M →ₗ[R] N') :
  M →ₗ[R] N × N' where
    toFun m := ⟨f m, g m⟩
    map_add' m n := by
      ext <;>
      simp
    map_smul' x m := by
      ext <;>
      simp



/- Exercise: define the following linear map -/
example (f : N →ₗ[R] M) (g : N' →ₗ[R] M) :
  N × N' →ₗ[R] M where
    toFun := fun ⟨n, n'⟩ => f n + g n'
    map_add' := by
      intro x y
      simp
      -- abel
      module
    map_smul' := by
      intro r x
      simp

example : M →ₗ[R] M × N := LinearMap.inl R M N
example : N →ₗ[R] M × N := LinearMap.inr R M N
example : M × N →ₗ[R] M := LinearMap.fst R M N
example : M × N →ₗ[R] N := LinearMap.snd R M N


-- The kernel of a linear map is a submodule, as is its range.
variable (f : M →ₗ[R] N)

#check LinearMap.ker f
#check LinearMap.range f


/- As with Subgroups, Subrings, and Ideals, Submodules
come with extra structure.
-/
example : CompleteLattice (Submodule R M) := by infer_instance


/-
A linear map is injective if and only if its kernel is trivial.
Note again the notation `⊥` for the zero submodule:
-/
#check (⊥ : Submodule R M)
example {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 := by exact Submodule.mem_bot R

#check (⊤ : Submodule R M)
#check Submodule.mem_top

example (f : M →ₗ[R] N) : LinearMap.ker f = ⊥ ↔ Injective f := LinearMap.ker_eq_bot

/- Exercise : write a similar condition characterization of surjective,
and find the lemma in mathlib.
 -/
example (f : M →ₗ[R] N) : LinearMap.range f = ⊤ ↔ Surjective f := by
  exact LinearMap.range_eq_top


/- Linear maps themselves form a module over `R`
(requires that `R` is a commutative ring) -/
example : Module R (M →ₗ[R] N) := by infer_instance

-- Exercise: is there any additional structure on `M →ₗ[R] M`?.
#synth Algebra R (M →ₗ[R] M)

/- If you want to use an operation that is linear in multiple arguments,
you can write it as a bundled morphism into the type of bundled morphisms. -/
#check LinearMap.lsmul R M
example (r : R) (m : M) : LinearMap.lsmul R M r m = r • m := by rfl
example (f : M →ₗ[R] N →ₗ[R] N') : N →ₗ[R] M →ₗ[R] N' := f.flip

/- We also have linear equivalences between modules: we write these as `M ≃ₗ[R] N` -/
#check M ≃ₗ[R] N

/- A linear equivalence sometimes must be converted explicitly to a linear map,
but in many cases a coercion to linear maps applies directly. -/
example (f : M ≃ₗ[R] N) : M →ₗ[R] N := f
example (f : M ≃ₗ[R] N) : Submodule R M := LinearMap.ker f.toLinearMap
example (f : M ≃ₗ[R] N) : Submodule R N := LinearMap.range f.toLinearMap


-- A linear equivalence is a linear map which is surjective and injective.
example (f : M →ₗ[R] N) (hf : Bijective f) : M ≃ₗ[R] N := LinearEquiv.ofBijective f hf

-- An injective linear map induces a linear equivalence to its range.
example (f : M →ₗ[R] N) (hf : Injective f) : M ≃ₗ[R] LinearMap.range f :=
  LinearEquiv.ofInjective f hf

-- Exercise: what happens if we just write `range f` above?



-- The **first isomorphism theorem** for modules: the quotient of M by ker f is equivalent
-- to the range of f.
example (f : M →ₗ[R] N) : (M ⧸ (LinearMap.ker f)) ≃ₗ[R] LinearMap.range f :=
  f.quotKerEquivRange

-- In particular, for a surjective linear map, the quotient of M by ker f is equivalent to N.
example {f : M →ₗ[R] N} (hf : Surjective f) : (M ⧸ (LinearMap.ker f)) ≃ₗ[R] N :=
  f.quotKerEquivOfSurjective hf


/- ## Linear algebra: endomorphisms, trace and determinant, and matrices -/


/- Matrices are defined in Mathlib, but generally we prefer to work
abstractly with vector spaces (or modules) without choosing a basis.
Things are often easier when stated using linear maps than with matrices. -/
#check Matrix

open scoped Matrix


example {m n : Type*} (M : Matrix m n R) : Mᵀᵀ = M := rfl

-- For example, we can define the determinant and trace for an linear endomorphism,
-- not just for a matrix.
section

variable {m : Type*} (A : Matrix m m M) [DecidableEq m] [Fintype m] [CommRing M]

#check A.det

#check A.trace

#eval (!![(1 : ℤ),2; 3,4]).trace

variable {V : Type*} [AddCommGroup V] [Module R V] {f : V →ₗ[R] V}

#check f.det
#check f.trace R V

end

/- We use `ι → ℝ` to denote `ℝ^n` if `ι` has `n` elements.
However, it is nicer to work over an abstract (finite-dimensional)
vector space. -/
example {ι : Type*} (v : ι → ℝ) : v + v = 2 • v := by rw [two_smul]
example {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (v : V) : v + v = 2 • v := by rw [two_smul]

/- `Module.finrank` gives the dimension of a vector space. -/
#check Module.finrank R M

/- `Module.Basis ι R M` is a structure of a basis of a vector space.
It is given by an equivalence of `M` with `ι →₀ R`, which is the
(infinitary) coproduct of copies of `R`, vectors indexed by `ι`,
where only finitely many entries are nonzero. -/
example {ι : Type*} (b : Module.Basis ι R M) : M ≃ₗ[R] ι →₀ R := b.repr

open Module

example {ι : Type*} (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)


/- As said above, you should avoid working with matrices when you can use linear maps instead.
If you must absolutely convert to matrices, mathlib also ha this: given a choice of basis,
you can convert a linear map to its induced matrix. This only works in finite dimensions and
requires a technical condition (decidable equality) on the indexing type. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (f : V →ₗ[K] V) : Matrix ι ι K := LinearMap.toMatrix b b f

example  {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (f : V →ₗ[K] V) : f.det = (f.toMatrix b b).det :=
  (LinearMap.det_toMatrix b f).symm

/- ### Eigenvectors, eigenvalues etc. -/

variable {f : V →ₗ[K] V} {v : V} {a : K}
-- Is `v` an eigenvector for the value `a` of an endomorphism `f`?
#check End.HasEigenvector f a v
-- Is `a` an eigenvalue of an endomorphism `f`?
#check End.HasEigenvalue f a


-- If `v` is an eigenvector for `a`, then `a` is an eigenvalue.
example (hv : End.HasEigenvector f a v) : End.HasEigenvalue f a :=
  by exact End.hasEigenvalue_of_hasEigenvector hv

example (hv : End.HasEigenvector f a v) : f v = a • v := by
  exact hv.apply_eq_smul


-- The characteristic polynomial of a linear map (assuming `V` is finite-dimensional).
variable [FiniteDimensional K V] in
#check f.charpoly

-- The characteristic polynomial is monic, has degree n (where n is the dimension of V),
-- and its constant coefficient is (up to sign) the determinant,
-- i.e. the product of its eigenvalues.
#check LinearMap.charpoly_monic
#check LinearMap.charpoly_natDegree
#check LinearMap.det_eq_sign_charpoly_coeff
-- The first coefficient after the leading one is the opposite of the trace.
-- Polynomial.nextCoeff is the second-highest coefficient (or zero).
#check Matrix.trace_eq_neg_charpoly_nextCoeff
#check Polynomial.nextCoeff


-- The Cayley-Hamilton: evaluation the characteristic polynomial of f at f yields zero.
#check LinearMap.aeval_self_charpoly


end LinearAlgebra

-- END OF LECTURE
