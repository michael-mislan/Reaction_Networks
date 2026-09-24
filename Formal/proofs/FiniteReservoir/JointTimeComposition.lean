import proofs.FiniteCopyReactor.SourceSemigroup
import proofs.FiniteReservoir.SourceCycleMeasure

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

theorem joint_source_semigroup (collect : Bool) (V : ℝ) (M : ℕ) (params : Parameters M)
    (hV : 0 < V)  (f : (JointCounts M) → ℝ≥0∞)
    (hf : ∀ X,f X ≤ 1) (X : (JointCounts M)) (t u : NNReal) :
    jointSourceEndpoint collect V M params hV f X (t+u)=
      jointSourceEndpoint collect V M params hV
        (fun Y => jointSourceEndpoint collect V M params hV f Y u) X t := by
  apply chronological_endpoint_semigroup (fun Y : (JointCounts M) => reactorMass Y.1)
    (jointReactorNext collect) (jointReactorRate V M params)
    (joint_reactor_nonneg V M params hV) (joint_reactor_total_pos V M params hV) _ f hf X t u
  intro n
  obtain ⟨q,hq,hbound⟩ := reactor_locally_bounded M params V hV n
  exact ⟨⟨q,by linarith⟩,by change 0 < q; linarith,fun Y hY => hbound Y.1 hY⟩

/-- The analysis-only boundary at 11/4 disappears; collection starts exactly at time three. -/
theorem joint_source_cycle_two_phase (V : ℝ) (M : ℕ) (params : Parameters M) (hV : 0 < V) 
    (f : (JointCounts M) → ℝ≥0∞) (hf : ∀ X,f X ≤ 1) (X : (JointCounts M)) :
    jointSourceCycle V M params hV f X=
      jointSourceEndpoint false V M params hV
        (fun Y => jointSourceEndpoint true V M params hV f Y 1) X 3 := by
  have hg (Y) : jointSourceEndpoint true V M params hV f Y 1 ≤ 1 :=
    chronological_endpoint_le_one _ _ _ _ f hf Y 1
  have hh := joint_source_semigroup false V M params hV
    (fun Y => jointSourceEndpoint true V M params hV f Y 1) hg X (11/4) (1/4)
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] at hh
  exact hh.symm

/-- The sole mark switch is the requested collection boundary; chemistry is unrestricted in both phases. -/
def literalMarkedCycleKernel (V : ℝ) (M : ℕ) (params : Parameters M) (hV : 0 < V)  : Kernel (JointCounts M) (JointCounts M) :=
  jointEndpointKernel true V M params hV 1 ∘ₖ jointEndpointKernel false V M params hV 3

instance literalMarkedCycleKernel_markov (V : ℝ) (M : ℕ) (params : Parameters M) (hV : 0 < V)  :
    IsMarkovKernel (literalMarkedCycleKernel V M params hV) := by
  unfold literalMarkedCycleKernel
  infer_instance

theorem joint_source_cycle_kernel_literal (V : ℝ) (M : ℕ) (params : Parameters M) (hV : 0 < V) 
    (X : (JointCounts M)) : jointSourceCycleKernel V M params hV X=literalMarkedCycleKernel V M params hV X := by
  apply Measure.ext
  intro A hA
  rw [← joint_source_cycle_event]
  rw [joint_source_cycle_two_phase V M params hV _ (fun Y => by split_ifs <;> simp)]
  rw [joint_source_endpoint_kernel false V M params hV 3 (by norm_num)]
  simp_rw [joint_source_endpoint_kernel true V M params hV 1 (by norm_num)]
  change _=(jointEndpointKernel true V M params hV 1 ∘ₖ jointEndpointKernel false V M params hV 3) X A
  rw [Kernel.comp_apply' _ _ _ hA]
  apply lintegral_congr
  intro Y
  exact lintegral_indicator_one hA

end
end FiniteReservoir
