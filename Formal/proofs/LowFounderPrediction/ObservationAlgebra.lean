import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

namespace LowFounderPrediction.ObservationAlgebra
noncomputable section
open Polynomial

/-- Terminal mark for one detected-or-missed cell. The process-to-PGF identity
is a separate conventional argument; this module proves the mark algebra. -/
def detector (ρ : ℝ) : Polynomial ℝ := C (1-ρ) + C ρ * X

theorem detector_zero (ρ : ℝ) : (detector ρ).coeff 0 = 1-ρ := by
  simp only [detector, coeff_add, coeff_C, coeff_C_mul_X]
  norm_num

theorem detector_one (ρ : ℝ) : (detector ρ).coeff 1 = ρ := by
  simp only [detector, coeff_add, coeff_C, coeff_C_mul_X]
  norm_num

theorem detector_high (ρ : ℝ) (n : ℕ) (hn : 2 ≤ n) : (detector ρ).coeff n = 0 := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp only [detector, coeff_add, coeff_C, coeff_C_mul_X, if_neg h0, if_neg h1, add_zero]

/-- Two founders under a common two-point condition must be mixed after squaring. -/
theorem shared_condition_gap (w g₀ g₁ : ℝ) :
    w*g₀^2+(1-w)*g₁^2-(w*g₀+(1-w)*g₁)^2 = w*(1-w)*(g₀-g₁)^2 := by
  ring

theorem shared_condition_dominates (w g₀ g₁ : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    (w*g₀+(1-w)*g₁)^2 ≤ w*g₀^2+(1-w)*g₁^2 := by
  have hp : 0 ≤ w*(1-w)*(g₀-g₁)^2 :=
    mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (sq_nonneg _)
  linarith [shared_condition_gap w g₀ g₁]

/-- Failure accounting after conditioning on a data-dependent confidence event.
The bounds on the two joint pieces must come from the actual training/future law. -/
theorem inference_budget (failure goodPiece badPiece ε δ : ℝ)
    (hpart : failure ≤ goodPiece+badPiece) (hg : goodPiece ≤ ε*(1-δ))
    (hb : badPiece ≤ δ) : failure ≤ ε+(1-ε)*δ := by
  nlinarith

end
end LowFounderPrediction.ObservationAlgebra
