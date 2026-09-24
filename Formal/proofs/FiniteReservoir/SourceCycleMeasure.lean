import proofs.FiniteReservoir.SourceCycleTransfer

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

def jointEndpointKernel (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V)  (T : ℝ) :=
  chronologicalKernel (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (joint_reactor_total_pos V M p hV) T

instance jointEndpointKernel_markov (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M)
    (hV : 0 < V)  (T : ℝ) :
    IsMarkovKernel (jointEndpointKernel collect V M p hV T) := by
  unfold jointEndpointKernel
  infer_instance

theorem joint_source_endpoint_kernel (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M)
    (hV : 0 < V)  (T : ℝ) (hT : 0 ≤ T)
    (f : JointCounts M → ℝ≥0∞) (X : JointCounts M) :
    jointSourceEndpoint collect V M p hV f X T=
      ∫⁻ Y,f Y ∂jointEndpointKernel collect V M p hV T X :=
  chronological_endpoint_measure (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (joint_reactor_total_pos V M p hV) X T hT
    (joint_trajectory_nonexplosion collect V M p hV X) f

/-- Kernel composition passes the actual endpoint state, including counters, to the next phase. -/
def jointSourceCycleKernel (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V)  : Kernel (JointCounts M) (JointCounts M) :=
  (jointEndpointKernel true V M p hV 1 ∘ₖ jointEndpointKernel false V M p hV (1/4)) ∘ₖ
    jointEndpointKernel false V M p hV (11/4)

instance jointSourceCycleKernel_markov (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V)  :
    IsMarkovKernel (jointSourceCycleKernel V M p hV) := by
  unfold jointSourceCycleKernel
  infer_instance

theorem joint_source_cycle_kernel (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V) 
    (f : JointCounts M → ℝ≥0∞) (X : JointCounts M) :
    jointSourceCycle V M p hV f X=∫⁻ Y,f Y ∂jointSourceCycleKernel V M p hV X := by
  unfold jointSourceCycle jointSourceCycleKernel
  simp_rw [joint_source_endpoint_kernel true V M p hV 1 (by norm_num),
    joint_source_endpoint_kernel false V M p hV (1/4) (by norm_num),
    joint_source_endpoint_kernel false V M p hV (11/4) (by norm_num)]
  simp_rw [Kernel.lintegral_comp _ _ _ (measurable_of_countable f)]

theorem joint_source_cycle_event (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V) 
    (A : Set (JointCounts M)) (X : JointCounts M) :
    jointSourceCycle V M p hV (fun Y => if Y ∈ A then 1 else 0) X=
      jointSourceCycleKernel V M p hV X A := by
  rw [joint_source_cycle_kernel]
  exact lintegral_indicator_one (Set.to_countable A).measurableSet

end
end FiniteReservoir
