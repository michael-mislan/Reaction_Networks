import proofs.OptimalAffinityRealizability.GlobalRealizability
import proofs.OptimalAffinityRealizability.ResponseMinimum

namespace OptimalAffinityRealizability
noncomputable section

theorem productLogCoordinates_eq {n : ℕ} (source : SquareSource n)
    (z : Fin n → ℝ) :
    source.product.transpose.mulVec z = (responseMatrix source).transpose.mulVec
      (source.reactant.transpose.mulVec z) := by
  have hinj := reactantTranspose_mulVec_injective source
  have hz : responseTangent source (source.reactant.transpose.mulVec z) = z :=
    hinj (reactantResponse_responseTangent source _)
  rw [← productResponse_eq_responseMatrix_transpose_mulVec]
  simp only [productResponse, hz]

theorem reconstructedCurrent_normalized {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q z : Fin n → ℝ) (i : Fin n) :
    reconstructedLogReactionCurrent source J g q z i =
      (J * g i) * normalizedResponseCurrent (responseMatrix source) q
        (source.reactant.transpose.mulVec z) i := by
  unfold reconstructedLogReactionCurrent reconstructedLogForwardFlow
    reconstructedLogReverseFlow reconstructedForwardFlow reconstructedReverseFlow
    OptimalAffinityCorrected.reconstructedForwardFlux
    OptimalAffinityCorrected.reconstructedReverseFlux normalizedResponseCurrent
  simp only [Pi.sub_apply, productLogCoordinates_eq]
  ring

theorem stationary_commonResponseCurrent {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q z : Fin n → ℝ) (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hmode : ControlledProductionMode source g)
    (hz : GlobalStationaryFiber source J g q z) :
    ∀ i, normalizedResponseCurrent (responseMatrix source) q
      (source.reactant.transpose.mulVec z) i =
        controlledFluxAtLogState source J g q z / J := by
  have hc := current_eq_controlledProductionRay source g
    (reconstructedLogReactionCurrent source J g q z) hmode hz
  intro i
  have hi := congrFun hc i
  rw [reconstructedCurrent_normalized] at hi
  change J * g i * normalizedResponseCurrent _ _ _ i =
    controlledFluxAtLogState source J g q z * g i at hi
  apply (eq_div_iff (ne_of_gt hJ)).mpr
  nlinarith [hg i]

end
end OptimalAffinityRealizability
