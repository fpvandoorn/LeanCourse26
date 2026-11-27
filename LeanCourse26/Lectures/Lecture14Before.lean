module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open BigOperators Function Set Filter Topology TopologicalSpace MeasureTheory
noncomputable section

#click_suggestions

/- # Today: Filters -/










/- # How to formalize limits? -/


/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺`
* variations of the latter two with the additional assumption `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior:
`f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

This gives `64` notions of limits.

When we prove that two limits compose: if
`f x` tends to `y₀` when `x` tends to `x₀` and
`g y` tends to `z₀` when `y` tends to `y₀` then
`(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.
This lemma has 512 variants.

Obviously we don't want to prove this 512 times.
Solution: use filters.





# Definitions and examples

If `X` is a type, a filter `F : Filter X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following:
-/
section defs

variable {X : Type*} (F : Filter X)

#check (F.sets : Set (Set X))
#check (F.univ_sets : univ ∈ F.sets)
-- A filter is closed under taking supersets.
#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)
-- A filter is closed under finite intersections.
#check (F.inter_sets : ∀ {U V},
  U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets)



/-
Intuitively, the sets belonging to a filter are "big sets"

Here are some examples of filters:
-/

/- `(atTop : Filter ℕ)` is made of sets of `ℕ` containing
`{n | n ≥ N}` for some `N` -/
#check (atTop : Filter ℕ)
example (ns : Set ℕ) : ns ∈ atTop ↔ ∃ N, ∀ n ≥ N, n ∈ ns :=
  by exact mem_atTop_sets


/- `𝓝 x`, made of neighborhoods of `x` in a topological space -/
#check (𝓝 3 : Filter ℝ)
example (rs : Set ℝ) : rs ∈ 𝓝 3 ↔ ∃ U, U ⊆ rs ∧ IsOpen U ∧ 3 ∈ U :=
  by exact mem_nhds_iff


/- `μ.ae` is made of sets whose complement has zero measure
with respect to a measure `μ`. -/
#check (ae volume : Filter (ℝ × ℝ × ℝ))
example (S : Set (ℝ × ℝ × ℝ)) : S ∈ ae volume ↔ volume Sᶜ = 0 := by
  exact mem_ae_iff

/-
It may be useful to think of a filter on a type `X`
as a generalized element of `Set X`.
* `atTop` is the "set of very large numbers"
* `𝓝 x₀` is the "set of points very close to `x₀`."
* For each `s : Set X` we have the so-called *principal filter*
  `𝓟 s` consisting of all sets that contain `s`.
-/
example {s t : Set ℝ} : t ∈ 𝓟 s ↔ s ⊆ t :=
  by exact mem_principal


end defs

/- # Order -/

section order
variable {X : Type*} (F G : Filter X)

/- There is an order on the type of filters, coming from reverse
inclusion of the underlying sets -/
example : F ≤ G ↔ G.sets ≤ F.sets := by rfl


/-
This convention is consistent with the "generalized sets intuition".
-/
example {s t : Set X} : s ≤ t → 𝓟 s ≤ 𝓟 t := by
  apply monotone_principal

example {s t : Set X} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) := by
  apply inf_principal

example {s t : Set X} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) := by
  apply sup_principal

example : (⊤ : Filter X) = 𝓟 (univ : Set X) := by
  exact principal_univ.symm

example : (⊥ : Filter X) = 𝓟 (∅ : Set X) := by
  exact principal_empty.symm


/-
This says "a very large natural number is at least 10"
-/
example : atTop ≤ 𝓟 (Ici 10) := by
  exact iInf_le_iff.mpr fun b a ↦ a 10

/-
This says "a real number very close to and greater than `x`
is very close to `x`"
-/
example (x : ℝ) : 𝓝[>] x ≤ 𝓝 x := by
  exact nhdsWithin_le_nhds

end order

/- # Map and Comap -/

section map

variable {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y)

/- the *pushforward* of filters generalizes images of sets. -/
example : Filter X → Filter Y := by
  exact map f

example (t : Set Y) : t ∈ map f F ↔ f ⁻¹' t ∈ F := by
  exact mem_map

-- Let's check this really agrees with images of sets for principal filters.
example (s : Set X) : (𝓟 s).map f = 𝓟 (f '' s) := by
  exact map_principal


-- Mapping filters is monotone: if F ≤ F', then F.map f ≤ F'.map f
#check map_mono

-- Mapping filters composes
#check map_map



/- the *pullback* of filters generalizes preimages -/
example : Filter Y → Filter X :=
  Filter.comap f

example (s : Set X) : s ∈ comap f G ↔ ∃ t ∈ G, f ⁻¹' t ⊆ s := by
  exact mem_comap

example {X Y : Type*} (f : X → Y) {s : Set Y} : (𝓟 s).comap f = 𝓟 (f ⁻¹' s) := by
  exact comap_principal

-- This is again monotone and composes, but the composition is contravariant.
#check Filter.comap_mono
#check Filter.comap_comap


/- These form a *Galois connection* / adjunction -/
example : Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  exact map_le_iff_le_comap

-- Exercise: prove the composition law for `comap` from the
-- Galois connection property and `map_map`.
example {X Y Z : Type*} {f : Filter X} {m : Z → Y} {n : Y → X} :
    comap m (comap n f) = comap (n ∘ m) f := by
  sorry

end map

/- # Tendsto-/

section tendsto

variable {X Y : Type*} (f : X → Y)

/- Using these operations, we can define limits -/
def MyTendsto (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

lemma Tendsto_iff (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ t : Set Y, t ∈ G → f ⁻¹' t ∈ F := by
  exact tendsto_def

/- A sequence `u` converges to `x`-/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = y₀⁺` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) (𝓝[≥] y₀)

/- `\lim_{x → ∞} f x = y` -/
example (f : ℝ → ℝ) (y : ℝ) : Prop :=
  sorry

/- `\lim_{x → -∞} f x = ∞` -/
example (f : ℝ → ℝ) : Prop :=
  sorry

/- Now the following states all possible composition lemmas all at
once! -/
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by
  sorry


end tendsto

/- # Bases -/

/- How do we translate from the filter definition of limit
* `Tendsto f atTop (𝓝 x)`
to the definition we are used to?
* `∀ ε > 0, ∃ N, ∀ n ≥ N, |f n - x| < ε`

The key observation is that `atTop` is "generated" by sets `[N, ∞)`,
while `𝓝 x` is "generated" by sets of the form `(x - ε, x + e)`.

This leads to the notion of a basis.
-/

structure myBasis {α : Type*} (F : Filter α) where
  ι : Type*
  B : ι → Set α
  prop s : s ∈ F ↔ ∃ i : ι, B i ⊆ s

#check HasBasis
#check HasBasis.tendsto_iff

variable {X Y I J : Type*} (F : Filter X) (G : Filter Y)
  (FB : I → Set X) (GB : J → Set Y) (p : I → Prop) (q : J → Prop)
  (hF : F.HasBasis p FB) (hG : G.HasBasis q GB) (f : X → Y)

example : Tendsto f F G ↔
    ∀ j : J, q j → ∃ i : I, p i ∧ ∀ x : X, x ∈ FB i → f x ∈ GB j := by
  exact hF.tendsto_iff hG

#check atTop_basis
#check nhds_basis_Ioo_pos


/- # Eventually true

Filters also allow us to reason about things that are
"eventually true". If `F : Filter X` and `P : X → Prop` then
`∀ᶠ n in F, P n` means that `P n` is eventually true for `n` in `F`.
It is defined to be `{ x | P x } ∈ F`.

The following example shows that if `P n` and `Q n` hold for
sufficiently large `n`, then so does `P n ∧ Q n`.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

-- In more complicated examples, it's useful to separate the
-- bookkeeping from the mathematical content:
-- this is what the `filter_upwards` tactic is good for.
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  sorry

/- How can we express that two functions are eventually equal? -/
variable (f g : ℕ → ℝ) (x : ℝ)

#check ∀ᶠ x in atTop, f x = g x
#check (f =ᶠ[atTop] g)


example (h : f =ᶠ[atTop] g) (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto g atTop (𝓝 x) := by
  apply hf.congr'
  exact h
