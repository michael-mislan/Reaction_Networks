import proofs.OptimalAffinityRealizability.Source
import proofs.OptimalAffinityCorrected.ResponseProfile

namespace OptimalAffinityRealizability

open Matrix
noncomputable section

abbrev responseObjective {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) (f : Fin n → ℝ) : ℝ :=
  OptimalAffinityCorrected.responseObjective T g f

noncomputable abbrev responseProfileBound {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) : ℝ :=
  OptimalAffinityCorrected.responseProfileBound T g

theorem inheritedResponseBound {n : ℕ} (T : Fin n → Fin n → ℝ)
    (g : Fin n → ℕ) (f : Fin n → ℝ)
    (hf : OptimalAffinityCorrected.ForwardResponse T f) :
    responseProfileBound T g ≤ responseObjective T g f :=
  OptimalAffinityCorrected.responseProfileBound_le_objective T g f hf

def SameResponseRay {n : ℕ} (f f' : Fin n → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ f' = a • f

def LogProfileGauge {n : ℕ} (f : Fin n → ℝ) : Prop :=
  ∑ i, Real.log (f i) = 0

/-- The unique candidate common species log-tangent for a response column. -/
def responseTangent {n : ℕ} (source : SquareSource n) (f : Fin n → ℝ) : Fin n → ℝ := by
  letI : Invertible source.reactant.transpose :=
    Matrix.invertibleOfIsUnitDet source.reactant.transpose (by
      simpa using source.reactant_det_isUnit)
  exact source.reactant.transpose⁻¹.mulVec f

def responseMatrix {n : ℕ} (source : SquareSource n) : Matrix (Fin n) (Fin n) ℝ := by
  letI : Invertible source.reactant :=
    Matrix.invertibleOfIsUnitDet source.reactant source.reactant_det_isUnit
  exact source.reactant⁻¹ * source.product

def productResponse {n : ℕ} (source : SquareSource n) (f : Fin n → ℝ) : Fin n → ℝ :=
  source.product.transpose.mulVec (responseTangent source f)

/-- Applying the literal reactant response map recovers the prescribed
reaction response.  Thus invertibility removes any hidden tangent choice. -/
theorem reactantResponse_responseTangent {n : ℕ} (source : SquareSource n)
    (f : Fin n → ℝ) :
    source.reactant.transpose.mulVec (responseTangent source f) = f := by
  letI : Invertible source.reactant.transpose :=
    Matrix.invertibleOfIsUnitDet source.reactant.transpose (by
      simpa using source.reactant_det_isUnit)
  unfold responseTangent
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- In the frozen column convention the common tangent's product response is
exactly `Tᵀ f`, where `T = Splus⁻¹ Sminus`. -/
theorem productResponse_eq_responseMatrix_transpose_mulVec {n : ℕ}
    (source : SquareSource n) (f : Fin n → ℝ) :
    productResponse source f = (responseMatrix source).transpose.mulVec f := by
  letI : Invertible source.reactant :=
    Matrix.invertibleOfIsUnitDet source.reactant source.reactant_det_isUnit
  letI : Invertible source.reactant.transpose :=
    Matrix.invertibleOfIsUnitDet source.reactant.transpose (by
      simpa using source.reactant_det_isUnit)
  unfold productResponse responseMatrix responseTangent
  rw [Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.transpose_nonsing_inv]

def controlCovector {n : ℕ} (source : SquareSource n) (f : Fin n → ℝ) : ℝ :=
  responseTangent source f source.controlled

def PositiveControlNormalization {n : ℕ} (source : SquareSource n)
    (f : Fin n → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ (a • responseTangent source f) source.controlled = 1

/-- A response ray can be scaled to the physical controlled tangent `u_X=1`
by a positive scalar exactly when its control covector is positive. -/
theorem controlAccessible_iff_responseRay_normalizable {n : ℕ}
    (source : SquareSource n) (f : Fin n → ℝ) :
    PositiveControlNormalization source f ↔ 0 < controlCovector source f := by
  constructor
  · rintro ⟨a, ha, hnorm⟩
    change a * controlCovector source f = 1 at hnorm
    have hprod : 0 < a * controlCovector source f := by
      rw [hnorm]
      norm_num
    nlinarith
  · intro hcontrol
    refine ⟨(controlCovector source f)⁻¹, inv_pos.mpr hcontrol, ?_⟩
    change (controlCovector source f)⁻¹ * controlCovector source f = 1
    exact inv_mul_cancel₀ (ne_of_gt hcontrol)

end
end OptimalAffinityRealizability
