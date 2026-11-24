import Mathlib

namespace HasseMinkowski
-- lemma needed for step 1 and 2 of proof
lemma square_zero {K : Type*} [Field K] (a b : K) (ha : a ≠ 0)
    (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0) (h : a * x^2 + b * y^2 = 0) :
    IsSquare (-a * b) := by
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
    -- step 3


    sorry

-- https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf
-- what i want to show
    -- 1. y ≠ 0 (otherwise a·x² = 0, so x = 0 too, contradicting h5)
    -- 2. -ab is a square in ℝ, namely (a·x/y)²
    -- 3. so -ab > 0 (in ℚ)
    -- 4. for every prime p, -ab is a square in ℚ_p, so its p-adic valuation is even
    -- 5. positive with all valuations even ⇒ -ab = r² for some r ∈ ℚ
    -- 6. (r, a) is the rational solution: a·r² + b·a² = a·(-ab) + a²b = 0, and a ≠ 0

end HasseMinkowski
