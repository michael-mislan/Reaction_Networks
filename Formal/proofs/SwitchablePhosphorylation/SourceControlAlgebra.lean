import Mathlib

namespace SwitchablePhosphorylation

/-- Reconstructed mass-action fluxes at a positive source equilibrium. -/
theorem reconstructed_fluxes (s e z q r : ℝ)
    (hs : s ≠ 0) (he : e ≠ 0) (hz : z ≠ 0) :
    ((1 + r) * q / (s * e)) * s * e = (1 + r) * q ∧
    (r * q / z) * z = r * q ∧ (q / z) * z = q := by
  constructor
  · field_simp
  constructor <;> field_simp

/-- Each complex balance vanishes for every reverse ratio. -/
theorem common_equilibrium_balance (q r : ℝ) :
    (1 + r) * q - r * q - q = 0 := by ring

/-- A rational affine concentration patch stays positive under its margin. -/
theorem affine_patch_positive (x v s δ : ℝ)
    (hs : |s| ≤ δ) (margin : δ * |v| < x) : 0 < x + s * v := by
  have h : |s * v| ≤ δ * |v| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hs (abs_nonneg v)
  have h' := neg_abs_le (s * v)
  linarith

/-- Rank of the unfolding can be checked along the corrected Hopf branch. -/
theorem unfolding_rank_identity (ar as_ br bs : ℝ) (h : ar ≠ 0) :
    ar * (bs - br * as_ / ar) = ar * bs - as_ * br := by
  field_simp

/-- The positive kernel flux plus this correction realizes arbitrary pool
and complex velocities in one kinase/phosphatase pair. -/
theorem controlled_pair_velocity (Q u c d : ℝ) :
    ((Q + u) - Q = u) ∧
    ((2 * Q + u + c) - Q - (Q + u) = c) ∧
    ((2 * Q + d) - Q - Q = d) := by
  constructor
  · ring
  constructor <;> ring

theorem positive_corrected_flux (Q correction weight : ℝ)
    (hQ : |correction| < Q) (hw : 1 ≤ weight) :
    0 < Q * weight + correction := by
  have hpos : 0 < Q := lt_of_le_of_lt (abs_nonneg correction) hQ
  have hmul : Q ≤ Q * weight := by nlinarith
  have h := neg_abs_le correction
  linarith

/-- Dividing a chosen positive flux by the path's mass-action monomial
realizes that flux exactly along the prescribed path. -/
theorem path_flux_realization (flux monomial : ℝ) (hm : monomial ≠ 0) :
    (flux / monomial) * monomial = flux := by field_simp

end SwitchablePhosphorylation
