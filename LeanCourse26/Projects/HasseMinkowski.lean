import Mathlib

namespace HasseMinkowski
-- lemma needed for step 1 and 2 of proof
lemma square_zero {K : Type*} [Field K] (a b : K) (ha : a ≠ 0)
  (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0) (h : a * x^2 + b * y^2 = 0) :
  IsSquare (-a * b) := by
    -- step 1: y ≠ 0
    have hy : y≠ 0 := by
      rintro rfl
      have h1 : a*x^2 = 0 := by
        linear_combination h
      have h2 : x = 0 := by
        simpa [ha] using h1
      simp [h2] at hxy
    -- step 2: -ab = (a x / y)²
    refine (isSquare_iff_exists_mul_self (-a * b)).mpr ?_
    use a*x/y
    rw [@div_mul_div_comm]
    rw[eq_div_iff]
    · linear_combination -a*h
    · exact mul_ne_zero hy hy

-- lemma needed for step 4 of proof
lemma even_padicValRat_of_IsSquare (p:ℕ) [Fact p.Prime] (q : ℚ) (hq : q ≠ 0)
  (h: IsSquare (q : ℚ_[p])): Even (padicValRat p q) := by
    obtain ⟨s, hs⟩ := h
    -- step 1: s≠ 0 since otherwise q=0
    have h1: s ≠ 0 := by
      rintro rfl
      apply hq
      simpa using hs
    -- v_p(q)= v(s*s) = v(s)+v(s)
    rw[← Padic.valuation_ratCast]
    rw[hs]
    rw[Padic.valuation_mul h1 h1]
    exact Even.add_self s.valuation

-- lemma needed for step 5 of proof
lemma pos_even_is_square (q:ℚ) (hq: 0 < q)
  (h: ∀ (p:ℕ) [Fact p.Prime], Even (padicValRat p q)): IsSquare q := by
  sorry

theorem Hasse_Minkowski_two (a b : ℚ) (ha: a ≠ 0) (hb : b ≠ 0):
  (∃ x y : ℚ, (x ≠ 0 ∨ y ≠ 0) ∧ a *x^2+b*y^2=0) ↔
  (∃ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) ∧ a * x^2 + b*y^2 = 0) ∧
  (∀ (p : ℕ) [Fact p.Prime], ∃ x y : ℚ_[p],
    (x ≠ 0 ∨ y ≠ 0) ∧ (a:ℚ_[p]) * x^2+b*y^2=0) := by
  constructor
  · rintro ⟨x, y, h1, h2⟩
    constructor
    · use x
      use y
      constructor
      · exact mod_cast h1
      · exact mod_cast h2
    · intro p h3
      use x
      use y
      constructor
      · exact mod_cast h1
      · exact mod_cast h2
  · rintro ⟨h1, h2⟩
    obtain ⟨x, h3⟩ := h1
    obtain ⟨y, h4⟩ := h3
    obtain ⟨h5, h6⟩ := h4
    have h7 : (a : ℝ) ≠ 0 := by exact mod_cast ha
    have h8 : (-a * b : ℚ) ≠ 0 := by simp [ha, hb]
    -- step 1 and 2
    have h9 : IsSquare ((-a * b : ℚ) : ℝ) := by
      have := square_zero (a : ℝ) (b : ℝ) h7 x y h5 h6
      exact mod_cast this
    unfold IsSquare at h9
    obtain ⟨z, h10⟩ := h9
    -- step 3
    have h11: (0:ℚ) < -a * b:= by
      have h12 : (0 : ℚ) ≤ ((-a *b : ℚ):ℝ) := by
        rw[h10]
        exact mod_cast mul_self_nonneg z
      have h13 : (0:ℚ) ≤ (-a*b) := by
        exact mod_cast h12
      exact Rat.lt_of_le_of_ne h13 (id (Ne.symm h8))
    -- step 4
    have h14: ∀ (p : ℕ) [Fact p.Prime], Even (padicValRat p (-a*b)) := by
      intro p h15
      obtain ⟨x_Q, y_Q, h16, h17⟩ := h2 p
      have h18 : (a : ℚ_[p]) ≠ 0 := by
        exact mod_cast ha
      have h19 : IsSquare ((-a*b : ℚ) : ℚ_[p]) := by
        have := square_zero (a : ℚ_[p]) (b:ℚ_[p]) h18 x_Q y_Q h16 h17
        exact mod_cast this
      exact even_padicValRat_of_IsSquare p (-a * b) h8 h19
    -- step 5
    have h20 := pos_even_is_square (-a*b) h11 h14
    obtain ⟨r, hr⟩ := h20
    -- step 6
    use r
    use a
    constructor
    · right
      assumption
    · linear_combination -a*hr

-- https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf
-- what i want to show
    -- 1. y ≠ 0 (otherwise a·x² = 0, so x = 0 too, contradicting h5)
    -- 2. -ab is a square in ℝ, namely (a·x/y)²
    -- 3. so -ab > 0 (in ℚ)
    -- 4. for every prime p, -ab is a square in ℚ_p, so its p-adic valuation is even
    -- 5. positive with all valuations even ⇒ -ab = r² for some r ∈ ℚ
    -- 6. (r, a) is the rational solution: a·r² + b·a² = a·(-ab) + a²b = 0, and a ≠ 0

end HasseMinkowski
