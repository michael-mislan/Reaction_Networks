import proofs.SerialTransferSelection.ShareGeometry

namespace SerialTransferSelection

/-- Exact two-type normalization. This uses both transfer intervals instead of
bounding the denominator by the sum of two upper bounds. -/
theorem normalized_share_lower (B W X Y r ε : ℝ)
    (hB : 0 ≤ B) (hBW : B ≤ W) (hW : 0 < W)
    (hXY : 0 < X+Y)
    (he : 0 ≤ ε) (he1 : ε < 1)
    (hl : (1-ε)*r*B ≤ X) (hu : Y ≤ (1+ε)*r*(W-B)) :
    (1-ε)*B/((1+ε)*W-2*ε*B) ≤ X/(X+Y) := by
  have hm : 0 < 1-ε := by linarith
  have hp : 0 < 1+ε := by linarith
  have hd : 0 < (1+ε)*W-2*ε*B := by
    have hh := mul_le_mul_of_nonneg_left hBW (by positivity : 0 ≤ 2*ε)
    nlinarith [mul_pos hm hW]
  apply (div_le_div_iff₀ hd hXY).mpr
  have h1 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (1+ε)*(W-B))
  have h2 := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ (1-ε)*B)
  nlinarith only [h1,h2]

/-- For the corrected balanced recurrence, r=(204/49)^j. Exact denominator
bookkeeping gives at most 155/154 improvement and leaves the geometric base. -/
theorem normalization_improvement_cap (r : ℝ) (hr : 1 ≤ r) :
    1/(2*r) ≤ 1/((308*r+2)/155) ∧
      1/((308*r+2)/155) ≤ (155/154)*(1/(2*r)) := by
  have hpos : 0 < r := by linarith
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    linarith
  · have hh : 1/((308*r+2)/155) ≤ 1/((308/155)*r) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    convert hh using 1
    field_simp
    ring

/-- A conservation-only countermodel; no claim about its probability under C3. -/
theorem conservation_quarter_sharp (a : ℝ) (ha : 1/4 < a) :
    ¬ (a*((4 : ℝ)/(4+4)) ≤ (4 : ℝ)/(4+28)) := by
  norm_num
  linarith

end SerialTransferSelection
