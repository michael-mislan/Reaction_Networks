import proofs.OptimalAffinityRealizability.PowerGlobalFamily

namespace OptimalAffinityRealizability

noncomputable section

def tangentGapCurrent (a : ℝ) (phi : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 + a * (y - 1)) / phi y

/-- A finite, source-checkable globality certificate: a positive denominator
lies above its tangent numerator and touches it only at the normalized state. -/
structure StrictTangentGapCertificate (a : ℝ) (phi : ℝ → ℝ) : Prop where
  positive : ∀ y, 0 < y → 0 < phi y
  tangentAtOne : phi 1 = 1
  gap : ∀ y, 0 < y → 1 + a * (y - 1) ≤ phi y
  uniqueTouch : ∀ y, 0 < y →
    1 + a * (y - 1) = phi y → y = 1

theorem tangentGapCurrent_le_one (a : ℝ) (phi : ℝ → ℝ)
    (cert : StrictTangentGapCertificate a phi)
    (y : ℝ) (hy : 0 < y) : tangentGapCurrent a phi y ≤ 1 := by
  unfold tangentGapCurrent
  exact (div_le_one (cert.positive y hy)).2 (cert.gap y hy)

theorem tangentGapCurrent_eq_one_iff (a : ℝ) (phi : ℝ → ℝ)
    (cert : StrictTangentGapCertificate a phi)
    (y : ℝ) (hy : 0 < y) : tangentGapCurrent a phi y = 1 ↔ y = 1 := by
  constructor
  · intro heq
    have htouch : 1 + a * (y - 1) = phi y := by
      unfold tangentGapCurrent at heq
      exact (div_eq_one_iff_eq (ne_of_gt (cert.positive y hy))).mp heq
    exact cert.uniqueTouch y hy htouch
  · rintro rfl
    unfold tangentGapCurrent
    rw [cert.tangentAtOne]
    norm_num

/-- The existing integer-power proof instantiates the abstract tangent-gap
mechanism with slope `d` and denominator `y^d`. -/
theorem powerFamily_strictTangentGapCertificate (d : ℕ) (hd : 2 ≤ d) :
    StrictTangentGapCertificate (d : ℝ) (fun y => y ^ d) := by
  refine {
    positive := fun y hy => pow_pos hy d
    tangentAtOne := by simp
    gap := ?_
    uniqueTouch := ?_
  }
  · intro y hy
    have hid := powerGapWeight_identity d y
    have hw := powerGapWeight_nonneg d y (le_of_lt hy)
    nlinarith [sq_nonneg (y - 1), mul_nonneg (sq_nonneg (y - 1)) hw]
  · intro y hy heq
    have hid := powerGapWeight_identity d y
    have hw := powerGapWeight_pos d hd y hy
    have hzero : (y - 1) ^ 2 * powerGapWeight d y = 0 := by
      nlinarith
    have hsquare : (y - 1) ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hw)
    nlinarith [sq_nonneg (y - 1)]

theorem powerFamilyCurrent_eq_tangentGapCurrent (d : ℕ) (y : ℝ) :
    powerFamilyCurrent d y =
      tangentGapCurrent (d : ℝ) (fun z => z ^ d) y := by
  unfold powerFamilyCurrent tangentGapCurrent
  congr 1
  ring

/-- The global power-family theorem is recovered from the reusable tangent-gap
interface rather than a family-specific optimization argument. -/
theorem powerFamily_globality_via_tangentGap (d : ℕ) (hd : 2 ≤ d)
    (y : ℝ) (hy : 0 < y) :
    powerFamilyCurrent d y ≤ 1 ∧
      (powerFamilyCurrent d y = 1 ↔ y = 1) := by
  rw [powerFamilyCurrent_eq_tangentGapCurrent]
  exact ⟨tangentGapCurrent_le_one _ _
      (powerFamily_strictTangentGapCertificate d hd) y hy,
    tangentGapCurrent_eq_one_iff _ _
      (powerFamily_strictTangentGapCertificate d hd) y hy⟩

end
end OptimalAffinityRealizability
