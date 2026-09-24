import Mathlib

namespace OptimalAffinityRealizability

open Matrix

/-- Literal square source data used by the realizability campaign.  Complex
matrices are species-by-reaction; responses are reaction columns. -/
structure SquareSource (n : ℕ) where
  reactant : Matrix (Fin n) (Fin n) ℝ
  product : Matrix (Fin n) (Fin n) ℝ
  forwardRate : Fin n → ℝ
  reverseRate : Fin n → ℝ
  controlled : Fin n
  reactant_nonnegative : ∀ i j, 0 ≤ reactant i j
  product_nonnegative : ∀ i j, 0 ≤ product i j
  forwardRate_positive : ∀ j, 0 < forwardRate j
  reverseRate_positive : ∀ j, 0 < reverseRate j
  reactant_det_isUnit : IsUnit (Matrix.det reactant : ℝ)
  netStoich_det_isUnit : IsUnit (Matrix.det (product - reactant) : ℝ)

def SquareSource.netStoich {n : ℕ} (source : SquareSource n) :
    Matrix (Fin n) (Fin n) ℝ :=
  source.product - source.reactant

def ControlledProductionMode {n : ℕ} (source : SquareSource n)
    (g : Fin n → ℝ) : Prop :=
  ∀ i, source.netStoich.mulVec g i = if i = source.controlled then 1 else 0

theorem netStoich_mulVec_injective {n : ℕ} (source : SquareSource n) :
    Function.Injective source.netStoich.mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  exact source.netStoich.isUnit_iff_isUnit_det.mpr source.netStoich_det_isUnit

end OptimalAffinityRealizability
