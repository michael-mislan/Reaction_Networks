import proofs.TypeII3.Algebra.PowSecant

namespace TypeIIL

open TypeII3

/-- Exact two-coordinate secant identity for the reverse monomial of a fork
reaction.  The chosen telescoping order keeps both coefficients positive on
positive states. -/
theorem fork_product_difference
    (P₁ P₂ R₁ R₂ : ℝ) (m : ℕ) :
    P₁ * R₁ ^ m - P₂ * R₂ ^ m =
      R₁ ^ m * (P₁ - P₂) +
        P₂ * secantPoly R₁ R₂ m * (R₁ - R₂) := by
  have hpow := pow_sub_pow_eq_mul_secantPoly R₁ R₂ m
  linear_combination P₂ * hpow

theorem fork_product_secant_coefficients_pos
    {P₂ R₁ R₂ : ℝ} {m : ℕ}
    (hP₂ : 0 < P₂) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hm : 0 < m) :
    0 < R₁ ^ m ∧ 0 < P₂ * secantPoly R₁ R₂ m := by
  exact ⟨pow_pos hR₁ m, mul_pos hP₂ (secantPoly_pos hR₁ hR₂ hm)⟩

/-- Fork secant-linearization preserves the arc cross determinant.  The
apparently dangerous product coefficient `U` cancels exactly; the second
secant coefficient contributes a strictly positive remainder. -/
theorem fork_secant_cross_pos
    {a b c g e k h U V : ℝ}
    (ha : 0 < a) (he : 0 < e) (hh : 0 < h) (hV : 0 < V)
    (hArcCross : 0 < (k * c) * b + a * (1 - k * g)) :
    0 < (k * c - h * U * a) * b +
      a * (1 - k * g + h * U * b + h * V * e) := by
  have hextra : 0 < a * h * V * e := by positivity
  nlinarith

/-- The coefficient of the next-current difference stays strictly positive,
and is strictly smaller than the corresponding local response contribution
when the physical response gain is strict. -/
theorem fork_secant_next_gain
    {h V e f : ℝ}
    (hh : 0 < h) (hV : 0 < V) (hf : 0 < f) (hfe : f < e) :
    0 < h * V * f ∧ h * V * f < h * V * e := by
  constructor
  · positivity
  · exact mul_lt_mul_of_pos_left hfe (mul_pos hh hV)

end TypeIIL
