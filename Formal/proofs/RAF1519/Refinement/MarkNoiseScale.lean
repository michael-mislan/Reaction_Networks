import proofs.RAF1519.Refinement.MarkConcentration

namespace RAF1519.Refinement
noncomputable section

def markTolerance : ℝ := 1/2000
def markThreshold : ℝ := (19/20)*markTolerance
def markTilt (V : ℝ) : ℝ := V*markThreshold/18

theorem mark_tilt_small (V : ℝ) (hV : 0 < V) :
    0 ≤ markTilt V ∧ markTilt V*(2/V) ≤ 1 := by
  constructor
  · unfold markTilt markThreshold markTolerance
    positivity
  · have he : markTilt V*(2/V) = (19/360000:ℝ) := by
      unfold markTilt markThreshold markTolerance
      field_simp
      ring
    rw [he]
    norm_num

theorem mark_interval_reserve (V : ℝ) (hV : 0 < V) (hlarge : 80000 ≤ V) :
    markThreshold+2/V ≤ markTolerance := by
  have hj : 2/V ≤ (1/40000:ℝ) := (div_le_iff₀ hV).mpr (by linarith)
  unfold markThreshold markTolerance
  linarith

theorem mark_optimized_exponent (V : ℝ) (hV : 0 < V) :
    -markTilt V*markThreshold+(markTilt V)^2*(9/(4*V))*4 = -(361/57600000000)*V := by
  unfold markTilt markThreshold markTolerance
  field_simp
  ring

theorem mark_exponent_margin (V : ℝ) (hV : 0 < V) :
    -markTilt V*markThreshold+(markTilt V)^2*(9/(4*V))*4 ≤ -V/160000000 := by
  rw [mark_optimized_exponent V hV]
  linarith

theorem mark_small_volume_trivial (V : ℝ) (hsmall : V ≤ 80000) :
    1 ≤ 2*ENNReal.ofReal (Real.exp (-V/160000000)) := by
  have he : (1:ℝ) ≤ 2*Real.exp (-V/160000000) := by
    have hh := Real.add_one_le_exp (-V/160000000)
    linarith
  have hh := ENNReal.ofReal_le_ofReal he
  simpa only [ENNReal.ofReal_one,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] using hh

end
end RAF1519.Refinement
