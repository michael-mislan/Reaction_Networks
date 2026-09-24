import proofs.SpecimenReliability.GateTradeoff

namespace SpecimenReliability
noncomputable section

/-- A reference pair shows at least one spurious positive with probability
`kappa`; the observed pair-acceptance probability is then `kappa+(1-kappa)*w`,
where `w` is the true at-least-one probability. -/
def fpAccept (kappa w : ℝ) : ℝ := kappa+(1-kappa)*w

/-- The multiplicative inflation of the certified level caused by spurious
positives. -/
def fpFactor (kappa H : ℝ) : ℝ := (1-kappa*H)/(1-kappa)

/-- The effective all-negative probability seen by the reduced gate curve. -/
def fpShift (kappa H : ℝ) : ℝ := H*(1-kappa)/(1-kappa*H)

/-- Spurious positives do not create a new optimisation problem: the observed
risk curve is an exact rescaling of the original gate curve, evaluated at the
observed acceptance probability and a shifted all-negative probability. -/
theorem fp_reduction (kappa H w : ℝ) (hk : kappa < 1) (hkH : kappa*H < 1) (m : ℕ) :
    (fpAccept kappa w)^m * (1-(1-H)*w)
      = fpFactor kappa H * gateCurve m (fpShift kappa H) (fpAccept kappa w) := by
  have h1 : (1:ℝ)-kappa ≠ 0 := ne_of_gt (sub_pos.mpr hk)
  have h2 : (1:ℝ)-kappa*H ≠ 0 := ne_of_gt (sub_pos.mpr hkH)
  unfold fpAccept fpFactor fpShift gateCurve
  field_simp
  ring

theorem fp_bound (kappa H w : ℝ) (m : ℕ) (hm : 1 ≤ m) (hk : 0 ≤ kappa)
    (hk1 : kappa < 1) (hH : 0 ≤ H ∧ H ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    (fpAccept kappa w)^m * (1-(1-H)*w)
      ≤ fpFactor kappa H * gateBound m (fpShift kappa H) := by
  have hkH : kappa*H < 1 := by nlinarith [hH.1, hH.2]
  have hd : (0:ℝ) < 1-kappa*H := by linarith
  have hc : (0:ℝ) < 1-kappa := by linarith
  have hHs : 0 ≤ fpShift kappa H ∧ fpShift kappa H ≤ 1 := by
    constructor
    · exact div_nonneg (mul_nonneg hH.1 (by linarith)) (le_of_lt hd)
    · rw [fpShift, div_le_one hd]
      nlinarith [hH.2]
  have hv : 0 ≤ fpAccept kappa w ∧ fpAccept kappa w ≤ 1 := by
    constructor
    · have : 0 ≤ (1-kappa)*w := mul_nonneg (by linarith) hw.1
      unfold fpAccept; linarith
    · have : (1-kappa)*w ≤ (1-kappa)*1 :=
        mul_le_mul_of_nonneg_left hw.2 (by linarith)
      unfold fpAccept; linarith
  have hA : 0 ≤ fpFactor kappa H := div_nonneg (by linarith) (le_of_lt hc)
  rw [fp_reduction kappa H w hk1 hkH m]
  exact mul_le_mul_of_nonneg_left (gate_maximum m hm _ _ hHs hv) hA

/-- At `K = 6` targets, recovery `a = 9/20` (so `H = (11/20)^6`) and `m = 9`
reference pairs, a spurious-positive rate of `1/300` still certifies the level
`1/20`. -/
theorem fp_example_safe :
    fpFactor (1/300) ((11/20:ℝ)^6) * gateBound 9 (fpShift (1/300) ((11/20:ℝ)^6))
      ≤ 1/20 := by
  norm_num [fpFactor, fpShift, gateBound, gateOpt, gateCurve]

/-- A spurious-positive rate of `1/250` is already too large: some admissible
true acceptance probability pushes the observed risk above `1/20`. -/
theorem fp_example_unsafe :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧
      1/20 < (fpAccept (1/250) w)^9 * (1-(1-(11/20:ℝ)^6)*w) := by
  refine ⟨37/40, by norm_num, by norm_num, ?_⟩
  norm_num [fpAccept]

end
end SpecimenReliability
