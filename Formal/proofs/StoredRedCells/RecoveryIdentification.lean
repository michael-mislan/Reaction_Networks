import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A conditional identification theorem motivated by Harper's printed
day-35 regression. The line is an explicitly adopted model, not an assertion
that the experimental observations are exact. No physiological rate range or
absolute Prx pool calibration is established by this file. -/
namespace StoredRedCells.Recovery
noncomputable section

def observed (rho t : ℝ) : ℝ := 1-rho*t
def oxidation (rho k t : ℝ) : ℝ := k * observed rho t-rho
def grossReduction (rho k t : ℝ) : ℝ := k * observed rho t
def observedIntegral (rho horizon : ℝ) : ℝ := horizon-rho*horizon^2/2

theorem net_rate_identical (rho k t : ℝ) :
    oxidation rho k t - grossReduction rho k t = -rho := by
  dsimp [oxidation, grossReduction]
  ring

/-- The endpoint condition is necessary and sufficient for nonnegative hidden
oxidation throughout this decreasing affine trace. -/
theorem nonnegative_oxidation_iff (rho k horizon : ℝ)
    (hr : 0 ≤ rho) (hk : 0 ≤ k) (hT : 0 ≤ horizon) :
    (∀ t, 0 ≤ t → t ≤ horizon → 0 ≤ oxidation rho k t) ↔
      rho ≤ k * observed rho horizon := by
  constructor
  · intro h
    have he := h horizon hT (le_refl horizon)
    dsimp [oxidation] at he
    linarith
  · intro he t _ht htT
    have hm : rho*t ≤ rho*horizon := mul_le_mul_of_nonneg_left htT hr
    have hy : observed rho horizon ≤ observed rho t := by
      dsimp [observed]
      linarith
    have hm2 := mul_le_mul_of_nonneg_left hy hk
    dsimp [oxidation]
    linarith

/-- A measured upper bound on gross reducing input bounds the hidden rate.
When NADPH changes or other sinks are present, B must be corrected using their
actual balance before this theorem is applied. -/
theorem finite_input_upper (rho k horizon B : ℝ)
    (hI : 0 < observedIntegral rho horizon)
    (hB : k * observedIntegral rho horizon ≤ B) :
    k ≤ B / observedIntegral rho horizon := by
  exact (le_div_iff₀ hI).mpr hB

/-- Two rates consistent with one gross-input measurement of tolerance eps
have a quantitative bounded difference. This is a bound, not source validation. -/
theorem input_measurement_separates (k1 k2 integral measured eps : ℝ)
    (h1lo : measured-eps ≤ k1*integral)
    (h1hi : k1*integral ≤ measured+eps)
    (h2lo : measured-eps ≤ k2*integral)
    (h2hi : k2*integral ≤ measured+eps) :
    -(2*eps) ≤ (k1-k2)*integral ∧ (k1-k2)*integral ≤ 2*eps := by
  constructor <;> nlinarith

/-- A calibrated residual-oxidation assay also bounds k without falsely
identifying net recovery with intrinsic reduction. -/
theorem oxidation_measurement_separates (rho y k1 k2 lo hi : ℝ)
    (h1lo : lo ≤ k1*y-rho) (h1hi : k1*y-rho ≤ hi)
    (h2lo : lo ≤ k2*y-rho) (h2hi : k2*y-rho ≤ hi) :
    -(hi-lo) ≤ (k1-k2)*y ∧ (k1-k2)*y ≤ hi-lo := by
  constructor <;> nlinarith

theorem printed_day35_constants :
    observed (2/315) 25 = (53/63 : ℝ) ∧
    observedIntegral (2/315) 25 = (1450/63 : ℝ) ∧
    (2/265 : ℝ) * observed (2/315) 25 = 2/315 := by
  norm_num [observed, observedIntegral]

/-- Exact finite input costs for the diagnostic alternatives. No claim that
the real preparations admit either cost is included. -/
theorem diagnostic_costs :
    (2/265 : ℝ)*observedIntegral (2/315) 25 = 580/3339 ∧
    (4/265 : ℝ)*observedIntegral (2/315) 25 = 1160/3339 := by
  norm_num [observedIntegral]

end
end StoredRedCells.Recovery
