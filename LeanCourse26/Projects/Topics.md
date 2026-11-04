# Suggested topics for Project 2

*We will fill this out more over the next week*.

<!-- * In **analysis**: the Fourier transform and convolution have been defined in mathlib. Show that the Fourier transform of a convolution is the product of Fourier transforms. -->

* In **calculus**: prove the gradient theorem for Euclidean space, also know as the fundamental theorem of calculus for line integrals. As stretch goals use it to prove the equivalence of two definitions of a conservative vector field and provide an example of a non-conservative vector field.

* In **real analysis**:
  - show that the Weierstrass function is continuous but nowhere differentiable.
  `tendstoUniformly_tsum` and `TendstoUniformly.continuous` will be useful to show the continuity.
  - show that nowhere differentiable functions are dense in the space of continuous functions
  - prove **Tikhonov’s theorem:** let K be a nonempty compact set in a normed space. Then any continuous function K → K has a fixed point

* In **complex analysis**
  - Prove that the Laurent series for a complex function converges on an annulus.

* In **combinatorics**: prove **Schur’s theorem:** for any coloring of the natural numbers in finitely many colors, there exists a monochromatic triple x, y, z such that x + y = z.

* In **commutative algebra**: Prove the [Krull–Akizuki theorem](https://en.wikipedia.org/wiki/Krull%E2%80%93Akizuki_theorem)

* In **Computability**
  * Show that the problem “is x = 1 in a given semigroup defined by generators and relations?” is undecidable.
  * **Computational complexity:** this area is in an early stage in Mathlib. Currently, only the class **P** is defined. You could define **NP** and provide an example of an NP-hard problem (even a trivial one — or try the Cook–Levin theorem).

* In **differential geometry**
  - define differential 1-forms and exact 1-forms (closed 1-forms are harder to define).
    Show that on a simply connected domain, every 1-form is exact. (Mathlib is still missing a general definition of n-forms, but that is too hard for a project)
  - Prove that a diffeomorphism between connected manifolds is either orientation-preserving or orientation-reversing (copy-paste the definition of orientable manifold from Mathlib PR [#16239](https://github.com/leanprover-community/mathlib4/pull/16239/files) and assume your manifolds have no boundary).
  - prove (parts of the) classification of connected 1-manifolds. (We can provide a good reference to start.)
  - define quotients of manifolds: if G is a discrete group acting properly on a manifold M, prove that the quotient M/G is a smooth manifold. Option/stretch goal: construct the real projective space from the sphere.

* In **hyperbolic geometry** define the Poincaré model of hyperbolic geometry - either the disc model or the half-plane model (or another model altogether), and show that is satisfies most of Euclid's axioms for geometry, but that the parallel postulate fails.

* In **planar geometry** many results are missing. Choose one: Desargues's theorem, Feuerbach's theorem, Menelaus's theorem, Morley's trisecor theorem.

* In **group theory**, study concrete group presentations. Mathlib has a `PresentedGroup` structure, but no concrete examples yet. For example, you could formalize the presentation of the permutation group (or others from [here](https://en.wikipedia.org/wiki/Presentation_of_a_group#Examples).

* In **linear algebra**/**geometry**: prove the **Cartan–Dieudonné theorem:** every isometry of ℝⁿ can be represented as a composition of at most n reflections.

* In **linear algebra**, prove Sylvester’s criterion for the positive definiteness of Hermitian matrices

* In **measure theory**, prove **Luzin’s theorem:** a function f is measurable on [0, 1] if and only if for every ε > 0, there exists a compact set of measure greater than 1 − ε on which f is continuous.

* In **model theory**: complete types of a language are defined in mathlib. Prove for a countable theory that if there are uncountably many types with `n` free variables, then there are continuum many. Or harder: show that in this case that the theory has continuum many non-isomorphic models.

* In **number theory**:
  - Prove the Hasse-Minkowski theorem for quadratic forms of the form `a_1*X_1^2 + a_2 * X_2^2`. If you have time, prove the `n = 3` case `(a_1*X_1^2 + a_2 * X_2^2 + a_3 * X_3^2)`.
  - Solve some diophantine equations. For example: show that there are no nonzero integer solutions to `x^4-y^4=z^2`. Find all solutions to `x^2+y^2=z^3` and to `|2^k-3^l|=1`.
  - **Hurwitz’s theorem** ([ProofWiki link](https://proofwiki.org/wiki/Hurwitz%27s_Theorem_(Number_Theory))) on approximating irrational numbers by rationals.

* In **set theory**: Define weakly compact cardinals, and prove that some other (combinatorial) properties are equivalent to this definition, e.g. properties 1-4 from [Wikipedia](https://en.wikipedia.org/wiki/Weakly_compact_cardinal).

* In **topology**:
  - [general topology] Define the Möbius strip and/or the Klein bottle and prove basic properties (e.g.: different constructions are equivalent; boundary of Möbius strip is connected and homotopy equivalent to `S¹`)
  Optional: prove they are smooth manifolds (with boundary).
  - [general topology] Define the [long line](https://en.wikipedia.org/wiki/Long_line_(topology)) and show that it is a topological manifold that is not separable. If time permits, show that it is sequentially compact, but not compact, or show other properties from [this list](https://topology.pi-base.org/spaces/S000038).
  - [general topology] Define some spaces that are typically used for counterexamples, such as the Hawaiian earring, wild knots or the horned sphere, and (dis)prove some topological properties for them.
  - [algebraic topology] Mathlib has a definition of simplicial complexes. Define oriented simplices and simplicial homology (if useful you can define abstract simplicial complexes yourself and do it for that definition).
  - [algebraic topology] Mathlib has a definition of singular homology: prove that is satisfies the homotopy invariance axiom. (The definition of singular homology uses abstract category theory machinery, so this is more suitable if you have used Lean before.)
  - [algebraic topology] Define n-connected spaces and n-connected maps (by defining the homotopy fiber of a (continuous) map). Prove that for spaces: 0-connected = path connected and 1-connected = simply connected. Try to prove some other easy properties, but beware that many properties are hard, since Mathlib doesn't have homology, Borsuk-Ulam or cellular approximation yet.
