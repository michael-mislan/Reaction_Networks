import proofs.OptimalAffinityRealizability.GlobalNormalization

namespace OptimalAffinityRealizability
open scoped BigOperators
noncomputable section

theorem controlCovector_eq_productionWeightedResponseGap {n : ℕ}
    (source : SquareSource n) (g f : Fin n → ℝ)
    (hmode : ControlledProductionMode source g) :
    controlCovector source f = ∑ i, g i *
      ((responseMatrix source).transpose.mulVec f i - f i) := by
  let u := responseTangent source f
  have hm : source.netStoich.mulVec g = Pi.single source.controlled 1 := by
    funext i
    simpa [Pi.single_apply, eq_comm] using hmode i
  have hc : dotProduct u (source.netStoich.mulVec g) = controlCovector source f := by
    rw [hm]
    simp [dotProduct, controlCovector, u, Pi.single_apply, mul_ite]
  have hn : source.netStoich.transpose.mulVec u =
      fun i => (responseMatrix source).transpose.mulVec f i - f i := by
    rw [SquareSource.netStoich, Matrix.transpose_sub, Matrix.sub_mulVec]
    rw [show source.reactant.transpose.mulVec u = f from reactantResponse_responseTangent source f]
    rw [show source.product.transpose.mulVec u = (responseMatrix source).transpose.mulVec f from
      productResponse_eq_responseMatrix_transpose_mulVec source f]
    rfl
  rw [← hc, ← Matrix.dotProduct_transpose_mulVec, hn]
  rfl

theorem positiveProduction_controlAccessible {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (g f : Fin n → ℝ)
    (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hf : ResponseFeasible (responseMatrix source) f) : ControlAccessible source f := by
  change 0 < controlCovector source f
  rw [controlCovector_eq_productionWeightedResponseGap source g f hmode]
  apply Finset.sum_pos
  · intro i _
    apply mul_pos (hg i)
    have hq := (hf i).2
    unfold OptimalAffinityCorrected.responseRatio at hq
    rw [responseImage_eq_transpose_mulVec] at hq
    have := (lt_div_iff₀ (hf i).1).mp hq
    linarith
  · exact Finset.univ_nonempty

end
end OptimalAffinityRealizability
