import proofs.CellTreatmentDecision.SeedThreshold

namespace CellTreatmentDecision

theorem error_to_sign (d approx err : ℝ) (bound : |d-approx| ≤ err)
    (margin : approx < -err) : d < 0 := by
  have h := (abs_le.mp bound).2
  linarith

theorem repeated_margin :
    (17209/504210000:ℝ) < 992063/5033164800 ∧
    (17209/504210000:ℝ) < 2438393/5033164800 := by norm_num

/-- Cubic coefficients from the conventional source-to-Taylor derivation. -/
theorem pulse_mixed (c cross : ℝ) :
    ((9+4*c)/3+4*9/3+cross)-(9/3+4*(9+4*c)/3+cross) = -4*c := by ring

theorem pulse_certified_margin (h : ℝ) (hpos : 0 < h)
    (hsmall : h ≤ 1/1000000) :
    64000*h^4 < (4/5:ℝ)*h^3 := by
  have h3 : 0 < h^3 := pow_pos hpos 3
  have hn : 64000*h < (4/5:ℝ) := by linarith
  have hm := mul_lt_mul_of_pos_right hn h3
  nlinarith [hm]

theorem balanced_regret (L U : ℝ) (hl : L < 0) (hu : 0 < U) :
    (-L/(U-L))*U = (1-(-L/(U-L)))*(-L) := by
  have hd : U-L ≠ 0 := by linarith
  field_simp
  ring

end CellTreatmentDecision
