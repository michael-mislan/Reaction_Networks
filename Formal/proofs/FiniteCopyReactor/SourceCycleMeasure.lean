import proofs.FiniteCopyReactor.SourceCycleTransfer

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

def jointEndpointKernel (collect : Bool) (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (T : ℝ) :=
  chronologicalKernel (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd) T

instance jointEndpointKernel_markov (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (T : ℝ) :
    IsMarkovKernel (jointEndpointKernel collect V r d hV hr hd T) := by
  unfold jointEndpointKernel
  infer_instance

theorem joint_source_endpoint_kernel (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (T : ℝ) (hT : 0 ≤ T)
    (f : JointCounts → ℝ≥0∞) (X : JointCounts) :
    jointSourceEndpoint collect V r d hV hr hd f X T=
      ∫⁻ Y,f Y ∂jointEndpointKernel collect V r d hV hr hd T X :=
  chronological_endpoint_measure (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd) X T hT
    (joint_trajectory_nonexplosion collect V r d hV hr hd X) f

/-- Kernel composition passes the actual endpoint state, including counters, to the next phase. -/
def jointSourceCycleKernel (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) : Kernel JointCounts JointCounts :=
  (jointEndpointKernel true V r d hV hr hd 1 ∘ₖ jointEndpointKernel false V r d hV hr hd (1/4)) ∘ₖ
    jointEndpointKernel false V r d hV hr hd (11/4)

instance jointSourceCycleKernel_markov (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    IsMarkovKernel (jointSourceCycleKernel V r d hV hr hd) := by
  unfold jointSourceCycleKernel
  infer_instance

theorem joint_source_cycle_kernel (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f : JointCounts → ℝ≥0∞) (X : JointCounts) :
    jointSourceCycle V r d hV hr hd f X=∫⁻ Y,f Y ∂jointSourceCycleKernel V r d hV hr hd X := by
  unfold jointSourceCycle jointSourceCycleKernel
  simp_rw [joint_source_endpoint_kernel true V r d hV hr hd 1 (by norm_num),
    joint_source_endpoint_kernel false V r d hV hr hd (1/4) (by norm_num),
    joint_source_endpoint_kernel false V r d hV hr hd (11/4) (by norm_num)]
  simp_rw [Kernel.lintegral_comp _ _ _ (measurable_of_countable f)]

theorem joint_source_cycle_event (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (A : Set JointCounts) (X : JointCounts) :
    jointSourceCycle V r d hV hr hd (fun Y => if Y ∈ A then 1 else 0) X=
      jointSourceCycleKernel V r d hV hr hd X A := by
  rw [joint_source_cycle_kernel]
  exact lintegral_indicator_one (Set.to_countable A).measurableSet

end
end FiniteCopyReactor
