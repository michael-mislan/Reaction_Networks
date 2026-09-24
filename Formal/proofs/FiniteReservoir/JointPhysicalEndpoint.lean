import proofs.FiniteReservoir.JointTimeComposition

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

def countEndpoint (V : ℝ) (M : ℕ) (params : Parameters M) (hV : 0 < V) 
    (f : (CountState M) → ℝ≥0∞) (N : (CountState M)) (T : ℝ) : ℝ≥0∞ :=
  chronologicalEndpoint reactorNext (reactorRate M params V)
    (reactor_rate_nonneg M params V hV) (reactor_total_pos M params V hV) f N T

theorem joint_endpoint_count_projection (collect : Bool) (V : ℝ) (M : ℕ) (params : Parameters M)
    (hV : 0 < V)  (f : (CountState M) → ℝ≥0∞) (X : (JointCounts M)) (T : ℝ) :
    jointSourceEndpoint collect V M params hV (fun Y => f Y.1) X T=
      countEndpoint V M params hV f X.1 T := by
  change (∫⁻ z,endpointObservable (fun Y : (JointCounts M) => f Y.1) T z
    ∂jointSourceTrajectory collect V M params hV X)=
      ∫⁻ z,endpointObservable f T z ∂reactorTrajectory M params V hV X.1
  rw [← joint_trajectory_projection collect V M params hV X]
  have hm : Measurable (endpointObservable (β := CompetitionChannel) f T) :=
    (endpoint_observable_measurable f).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hm
    (project_jump_path_measurable (fun Y : (JointCounts M) => Y.1) measurable_fst)]
  apply lintegral_congr
  intro z
  rfl

theorem count_endpoint_semigroup (V : ℝ) (M : ℕ) (params : Parameters M) (hV : 0 < V) 
    (f : (CountState M) → ℝ≥0∞) (hf : ∀ N,f N ≤ 1) (N : (CountState M)) (t u : NNReal) :
    countEndpoint V M params hV f N (t+u)=
      countEndpoint V M params hV (fun Y => countEndpoint V M params hV f Y u) N t := by
  apply chronological_endpoint_semigroup reactorMass reactorNext (reactorRate M params V)
    (reactor_rate_nonneg M params V hV) (reactor_total_pos M params V hV) _ f hf N t u
  intro n
  obtain ⟨q,hq,hbound⟩ := reactor_locally_bounded M params V hV n
  exact ⟨⟨q,by linarith⟩,by change 0 < q; linarith,hbound⟩

/-- Erasing the counters gives the unchanged count source at physical time four. -/
theorem joint_cycle_count_projection (V : ℝ) (M : ℕ) (params : Parameters M) (hV : 0 < V) 
    (f : (CountState M) → ℝ≥0∞) (hf : ∀ N,f N ≤ 1) (X : (JointCounts M)) :
    jointSourceCycle V M params hV (fun Y => f Y.1) X=
      countEndpoint V M params hV f X.1 4 := by
  rw [joint_source_cycle_two_phase V M params hV _ (fun Y => hf Y.1)]
  simp_rw [joint_endpoint_count_projection true V M params hV f]
  rw [joint_endpoint_count_projection false V M params hV
    (fun N => countEndpoint V M params hV f N 1)]
  have hh := count_endpoint_semigroup V M params hV f hf X.1 3 1
  norm_num only [NNReal.coe_ofNat,NNReal.coe_one] at hh
  exact hh.symm

end
end FiniteReservoir
