# Suggested topics for Project 2

You are encouraged to think of your own project.

* In **analysis**:
  - show that the Weierstrass function is continuous but nowhere differentiable.
  `tendstoUniformly_tsum` and `TendstoUniformly.continuous` will be useful to show the continuity.
  - show that nowhere differentiable functions on the reals are dense in the space of continuous functions
  - In multivariate analysis, prove some things about conservative vector fields. Using Mathlib’s `curveIntegral`, prove these are equivalent: path-independence, vanishing loop integrals, and being a gradient on a connected open set. Then show `(−y dx + x dy)/(x²+y²)` is closed but not exact on ℝ²∖{0}.
  - In complex analysis, prove that the Laurent series for a complex function converges on an annulus.

* In **commutative algebra**: Prove the [Krull–Akizuki theorem](https://en.wikipedia.org/wiki/Krull%E2%80%93Akizuki_theorem)

* **complexity theory** is hard in Lean, and there is no good setup at the moment. You can still define a reduction from 1-2 NP-hard problems in complexity theory to (e.g.) 3-SAT, and make sure this reduction is a computable definition in Lean. Showing complexity bounds formally is hard, but you can use a trick lime [`TimeM`](https://github.com/leanprover/cslib/blob/bdbd823028db6c316a0005d7f4cdf71aab4453ad/Cslib/Algorithms/Lean/TimeM.lean) to count how many "elementary steps" you need in the algorithm and show that the algorithm is polynomial in that number of steps.

* In **combinatorics**, prove the Loomis-Whitney inequality for lattices.

* In **algebraic geometry**, the company Axiom has a list of exercises [here](https://stacks.axiommath.ai/contributing). Some of these could be good starter projects. You are allowed, but not required, to submit your project in their system as well.

* In **differential geometry**
  - Show that on a simply connected domain, every closed 1-form is exact. (Mathlib is still missing a general definition of n-forms, but that is too hard for a project)
  - Prove that a diffeomorphism between connected manifolds is either orientation-preserving or orientation-reversing (copy-paste the definition of orientable manifold from Mathlib PR [#35376](https://github.com/leanprover-community/mathlib4/pull/35376) and assume your manifolds have no boundary).
  - prove (parts of the) classification of connected 1-manifolds.
  - define quotients of manifolds: if G is a discrete group acting properly on a manifold M, prove that the quotient M/G is a smooth manifold. Option/stretch goal: construct the real projective space from the sphere.
  - Take the inverse function theorem from [#34005](https://github.com/leanprover-community/mathlib4/pull/34005) as an axiom. From it, prove basic properties about immersions on manifolds.
  - (probably too hard) prove the inverse function theorem for manifolds with boundary.

* In **hyperbolic geometry** define the Upper half-plane model (it already exists as a metric space). Do one or both of (1) show that `PSL₂(ℝ)` acts by isometries; (2) with the vertical lines and semicircles as geodesics, show that the parallel postulate fails but the other axioms hold.

* In **planar geometry** many results are missing from Mathlib. Choose one: Desargues's theorem, Feuerbach's theorem, Menelaus's theorem, Morley's trisector theorem.

* In **planar geometry** prove the **Wallace–Bolyai–Gerwien theorem:** two polygons in the
plane are "cut-and-paste" equivalent if and only if they have the same area.

* In **graph theory** prove **Kirchoff's Theorem** which computes the number of spanning
trees in terms of the graph laplacian.

* In **group theory**, study concrete group presentations. Mathlib has a `PresentedGroup` structure, but no concrete examples yet. For example, you could formalize the presentation of the permutation group (or others from [here](https://en.wikipedia.org/wiki/Presentation_of_a_group#Examples).

* In **linear algebra**, prove Sylvester’s criterion for the positive definiteness of Hermitian matrices

* In **measure theory**, prove **Luzin’s theorem:** a function `f` is Lebesgue measurable on `[0, 1]` if and only if for every `ε > 0`, there exists a compact set of measure greater than `1 − ε` on which `f` is continuous.

* In **model theory**: complete types of a language are defined in mathlib. Prove for a countable theory that if there are uncountably many types with `n` free variables, then there are continuum many. Or harder: show that in this case that the theory has continuum many non-isomorphic models.

* In **number theory**:
  - Prove the Hasse-Minkowski theorem for quadratic forms of the form `a_1*X_1^2 + a_2 * X_2^2`. If you have time, prove the `n = 3` case `(a_1*X_1^2 + a_2 * X_2^2 + a_3 * X_3^2)`.
  - Solve some diophantine equations. For example: show that there are no nonzero integer solutions to `x^4-y^4=z^2`. Find all solutions to `x^2+y^2=z^3` and to `|2^k-3^l|=1`.
  - **Hurwitz’s theorem** ([ProofWiki link](https://proofwiki.org/wiki/Hurwitz%27s_Theorem_(Number_Theory))) on approximating irrational numbers by rationals.

* In **set theory**: Define weakly compact cardinals, and prove that some other (combinatorial) properties are equivalent to this definition, e.g. (some of) properties 1-4 from [Wikipedia](https://en.wikipedia.org/wiki/Weakly_compact_cardinal).

* In **general topology**:
  - Define the Möbius strip and/or the Klein bottle and prove basic properties (e.g.: different constructions are equivalent; boundary of Möbius strip is connected and homotopy equivalent to `S¹`)
  Optional: prove they are smooth manifolds (with boundary).
  - Define the [long line](https://en.wikipedia.org/wiki/Long_line_(topology)) and show that it is a topological manifold that is not separable. If time permits, show that it is sequentially compact, but not compact, or show other properties from [this list](https://topology.pi-base.org/spaces/S000038).
  - Define some spaces that are typically used for counterexamples, such as the Hawaiian earring, wild knots or the horned sphere, and (dis)prove some topological properties for them.
  - prove Brouwer's theorem: every compact perfect metrizable totally disconnected topological space is homeomorphic to the Cantor set
  - define the quotient of a CW-complex by a subcomplex (as a new CW-complex). Then prove that the (reduced) suspension and the smash product are CW-complexes.
  - prove one of these metrizability/normability conditions: Nagata–Smirnov metrization theorem; Bing metrization theorem; Kolmogorov's normability criterion

* In **algebraic topology**, Mathlib has a definition of simplicial complexes. Define oriented simplices and simplicial homology (if useful you can define abstract simplicial complexes yourself and do it for that definition).

**Miscellaneous**:
  - Define the decimal expansion of a real number, and prove a real number is rational
  if and only if it's decimal expansion is eventually periodic.
