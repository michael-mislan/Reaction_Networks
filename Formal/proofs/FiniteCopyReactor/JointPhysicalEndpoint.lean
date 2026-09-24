import proofs.FiniteCopyReactor.JointTimeComposition

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

def countEndpoint (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f : Counts → ℝ≥0∞) (N : Counts) (T : ℝ) : ℝ≥0∞ :=
  chronologicalEndpoint reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd) f N T

theorem joint_endpoint_count_projection (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (f : Counts → ℝ≥0∞) (X : JointCounts) (T : ℝ) :
    jointSourceEndpoint collect V r d hV hr hd (fun Y => f Y.1) X T=
      countEndpoint V r d hV hr hd f X.1 T := by
  change (∫⁻ z,endpointObservable (fun Y : JointCounts => f Y.1) T z
    ∂jointSourceTrajectory collect V r d hV hr hd X)=
      ∫⁻ z,endpointObservable f T z ∂reactorTrajectory V r d hV hr hd X.1
  rw [← joint_trajectory_projection collect V r d hV hr hd X]
  have hm : Measurable (endpointObservable (β := CompetitionChannel) f T) :=
    (endpoint_observable_measurable f).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hm
    (project_jump_path_measurable (fun Y : JointCounts => Y.1) measurable_fst)]
  apply lintegral_congr
  intro z
  rfl

theorem count_endpoint_semigroup (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f : Counts → ℝ≥0∞) (hf : ∀ N,f N ≤ 1) (N : Counts) (t u : NNReal) :
    countEndpoint V r d hV hr hd f N (t+u)=
      countEndpoint V r d hV hr hd (fun M => countEndpoint V r d hV hr hd f M u) N t := by
  apply chronological_endpoint_semigroup reactorMass reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd) _ f hf N t u
  intro n
  obtain ⟨q,hq,hbound⟩ := reactor_locally_bounded V r d hV hr hd n
  exact ⟨⟨q,by linarith⟩,by change 0 < q; linarith,hbound⟩

/-- Erasing the counters gives the unchanged count source at physical time four. -/
theorem joint_cycle_count_projection (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (f : Counts → ℝ≥0∞) (hf : ∀ N,f N ≤ 1) (X : JointCounts) :
    jointSourceCycle V r d hV hr hd (fun Y => f Y.1) X=
      countEndpoint V r d hV hr hd f X.1 4 := by
  rw [joint_source_cycle_two_phase V r d hV hr hd _ (fun Y => hf Y.1)]
  simp_rw [joint_endpoint_count_projection true V r d hV hr hd f]
  rw [joint_endpoint_count_projection false V r d hV hr hd
    (fun N => countEndpoint V r d hV hr hd f N 1)]
  have hh := count_endpoint_semigroup V r d hV hr hd f hf X.1 3 1
  norm_num only [NNReal.coe_ofNat,NNReal.coe_one] at hh
  exact hh.symm

end
end FiniteCopyReactor
