import proofs.FiniteCopyReactor.SourceSemigroup
import proofs.FiniteCopyReactor.SourceCycleMeasure

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

theorem joint_source_semigroup (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (f : JointCounts → ℝ≥0∞)
    (hf : ∀ X,f X ≤ 1) (X : JointCounts) (t u : NNReal) :
    jointSourceEndpoint collect V r d hV hr hd f X (t+u)=
      jointSourceEndpoint collect V r d hV hr hd
        (fun Y => jointSourceEndpoint collect V r d hV hr hd f Y u) X t := by
  apply chronological_endpoint_semigroup (fun Y : JointCounts => reactorMass Y.1)
    (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd) _ f hf X t u
  intro n
  obtain ⟨q,hq,hbound⟩ := reactor_locally_bounded V r d hV hr hd n
  exact ⟨⟨q,by linarith⟩,by change 0 < q; linarith,fun Y hY => hbound Y.1 hY⟩

/-- The analysis-only boundary at 11/4 disappears; collection starts exactly at time three. -/
theorem joint_source_cycle_two_phase (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f : JointCounts → ℝ≥0∞) (hf : ∀ X,f X ≤ 1) (X : JointCounts) :
    jointSourceCycle V r d hV hr hd f X=
      jointSourceEndpoint false V r d hV hr hd
        (fun Y => jointSourceEndpoint true V r d hV hr hd f Y 1) X 3 := by
  have hg (Y) : jointSourceEndpoint true V r d hV hr hd f Y 1 ≤ 1 :=
    chronological_endpoint_le_one _ _ _ _ f hf Y 1
  have hh := joint_source_semigroup false V r d hV hr hd
    (fun Y => jointSourceEndpoint true V r d hV hr hd f Y 1) hg X (11/4) (1/4)
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] at hh
  exact hh.symm

/-- The sole mark switch is the requested collection boundary; chemistry is unrestricted in both phases. -/
def literalMarkedCycleKernel (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) : Kernel JointCounts JointCounts :=
  jointEndpointKernel true V r d hV hr hd 1 ∘ₖ jointEndpointKernel false V r d hV hr hd 3

instance literalMarkedCycleKernel_markov (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    IsMarkovKernel (literalMarkedCycleKernel V r d hV hr hd) := by
  unfold literalMarkedCycleKernel
  infer_instance

theorem joint_source_cycle_kernel_literal (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (X : JointCounts) : jointSourceCycleKernel V r d hV hr hd X=literalMarkedCycleKernel V r d hV hr hd X := by
  apply Measure.ext
  intro A hA
  rw [← joint_source_cycle_event]
  rw [joint_source_cycle_two_phase V r d hV hr hd _ (fun Y => by split_ifs <;> simp)]
  rw [joint_source_endpoint_kernel false V r d hV hr hd 3 (by norm_num)]
  simp_rw [joint_source_endpoint_kernel true V r d hV hr hd 1 (by norm_num)]
  change _=(jointEndpointKernel true V r d hV hr hd 1 ∘ₖ jointEndpointKernel false V r d hV hr hd 3) X A
  rw [Kernel.comp_apply' _ _ _ hA]
  apply lintegral_congr
  intro Y
  exact lintegral_indicator_one hA

end
end FiniteCopyReactor
