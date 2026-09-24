import Mathlib.Tactic

/-! Shimo et al. (2011), DOI 10.1155/2011/398945, Eq (1).
This formalizes the literal rate law and a limitation of designed assays;
it does not assert that the examples are donor-matched preparations. -/
namespace G6PDReserve
noncomputable section

def shimoRate (V Kn Kg Kh Ka Kb N S H A B : ℝ) : ℝ :=
  (V * (N / Kn) * (S / Kg)) /
    (1 + (N / Kn) * (1 + S / Kg) + H / Kh + A / Ka + B / Kb)

/-- An entire inhibitor-free substrate surface is independent of all three
inhibition constants, not just independent at a finite list of tested points. -/
theorem uninhibited_surface_ambiguity (V Kn Kg Kh Ka Kb Lh La Lb N S : ℝ) :
    shimoRate V Kn Kg Kh Ka Kb N S 0 0 0 =
      shimoRate V Kn Kg Lh La Lb N S 0 0 0 := by
  simp [shimoRate]

theorem inhibition_separates_identical_surfaces :
    (∀ N S : ℝ, shimoRate 1 3 7 1 125 520 N S 0 0 0 =
      shimoRate 1 3 7 56 125 520 N S 0 0 0) ∧
    shimoRate 1 3 7 1 125 520 3 7 56 0 0 = 1/59 ∧
    shimoRate 1 3 7 56 125 520 3 7 56 0 0 = 1/4 := by
  constructor
  · intro N S; exact uninhibited_surface_ambiguity ..
  · norm_num [shimoRate]

/-- Multiplication by positive substrate and affinity factors converts the
printed source law to a polynomial denominator. -/
theorem source_rate_polynomial (V Kn Kg Kh Ka Kb N S H A B : ℝ)
    (hKn : Kn ≠ 0) (hKg : Kg ≠ 0) :
    shimoRate V Kn Kg Kh Ka Kb N S H A B =
    V*N*S / (Kn*Kg + N*Kg + N*S + Kn*Kg*(H/Kh+A/Ka+B/Kb)) := by
  unfold shimoRate
  field_simp
  ring

/-- The reciprocal rate is linear in six identifiable composite coefficients.
Positivity assumptions are needed when recovering parameters from coefficients;
this identity only needs the displayed nonzero parameters and substrates. -/
theorem reciprocal_source_rate (V Kn Kg Kh Ka Kb N S H A B : ℝ)
    (hV : V ≠ 0) (hN : N ≠ 0) (hS : S ≠ 0)
    (hKn : Kn ≠ 0) (hKg : Kg ≠ 0) :
    (shimoRate V Kn Kg Kh Ka Kb N S H A B)⁻¹ =
      1/V + (Kg/V)/S + (Kn*Kg/V)/(N*S) +
      (Kn*Kg/V)*(H/Kh+A/Ka+B/Kb)/(N*S) := by
  rw [source_rate_polynomial V Kn Kg Kh Ka Kb N S H A B hKn hKg]
  rw [inv_div]
  field_simp
  ring

end
end G6PDReserve
