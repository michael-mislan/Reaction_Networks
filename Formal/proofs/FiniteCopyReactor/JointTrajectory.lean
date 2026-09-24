import proofs.FiniteCopyReactor.JointCountSource
import proofs.FiniteCopyReactor.JumpProjection
import proofs.FiniteCopyReactor.ActualSource

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding Filter
open scoped ENNReal Topology

def jointSourceTrajectory (collect : Bool) (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (X : JointCounts) : Measure (ℕ → JumpState JointCounts CompetitionChannel) :=
  jumpTrajectoryLaw X (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd)

instance jointSourceTrajectory_probability (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (X : JointCounts) :
    IsProbabilityMeasure (jointSourceTrajectory collect V r d hV hr hd X) := by
  unfold jointSourceTrajectory
  infer_instance

/-- Erasing counters recovers the exact original count trajectory, including all waits and labels. -/
theorem joint_trajectory_projection (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (X : JointCounts) :
    (jointSourceTrajectory collect V r d hV hr hd X).map (projectJumpPath (fun Y : JointCounts => Y.1))=
      reactorTrajectory V r d hV hr hd X.1 :=
  project_jump_trajectory (fun Y : JointCounts => Y.1) measurable_fst
    (jointReactorNext collect) reactorNext (fun _ _ => rfl) (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd) X

theorem joint_trajectory_nonexplosion (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (X : JointCounts) :
    ∀ᵐ z ∂jointSourceTrajectory collect V r d hV hr hd X,Tendsto (jumpElapsed z) atTop atTop := by
  have hp : ∀ᵐ z ∂(jointSourceTrajectory collect V r d hV hr hd X).map
      (projectJumpPath (fun Y : JointCounts => Y.1)),Tendsto (jumpElapsed z) atTop atTop := by
    rw [joint_trajectory_projection]
    exact physical_jump_times_tendsto_atTop V r d hV hr hd X.1
  exact ae_of_ae_map (project_jump_path_measurable (fun Y : JointCounts => Y.1) measurable_fst).aemeasurable hp

/-- Counters do not change the physical process and record exactly the literal event marks. -/
theorem joint_actual_events (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (X : JointCounts) :
    ∀ᵐ z ∂jointSourceTrajectory collect V r d hV hr hd X,∀ k,∃ j : CompetitionChannel,
      (z (k+1)).2.1=Sum.inr j ∧
      0 < CommonPhysicalRealization.physicalRate (z k).1.1 V r d 1 1 j ∧
      (∀ i,reactants (competitionBase j) i ≤ (z k).1.1 i) ∧
      (z (k+1)).1.1=CommonPhysicalRealization.physicalNext (z k).1.1 j ∧
      ∀ i,(z (k+1)).1.2 i=(z k).1.2 i+integerCycleMarks collect j i := by
  have hp := actual_source_events V r d hV hr hd X.1
  rw [← joint_trajectory_projection collect V r d hV hr hd X] at hp
  have hh := ae_of_ae_map (project_jump_path_measurable (fun Y : JointCounts => Y.1) measurable_fst).aemeasurable hp
  have hc := jumpTrajectory_consistent X (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd)
  filter_upwards [hh,hc] with z hz hcons
  intro k
  obtain ⟨j,hj,hpos,havailable,hnext⟩ := hz k
  obtain ⟨l,hl,hn⟩ := hcons k
  have hlj : l=j := Sum.inr.inj (hl.symm.trans hj)
  subst l
  refine ⟨j,hj,hpos,havailable,hnext,?_⟩
  intro i
  rw [hn]
  rfl

theorem joint_source_endpoint_one (collect : Bool) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (X : JointCounts) (T : ℝ) (hT : 0 ≤ T) :
    jointSourceEndpoint collect V r d hV hr hd (fun _ => 1) X T=1 := by
  have hw := jumpTrajectory_wait_nonneg X (jointReactorNext collect) (jointReactorRate V r d)
    (joint_reactor_nonneg V r d hV hr hd) (joint_reactor_total_pos V r d hV hr hd)
  have hn := joint_trajectory_nonexplosion collect V r d hV hr hd X
  have he : ∀ᵐ z ∂jointSourceTrajectory collect V r d hV hr hd X,endpointObservable (fun _ => 1) T z=1 := by
    filter_upwards [hw,hn] with z hwait hdiv
    obtain ⟨k,hk⟩ := endpoint_interval_exists z T hT hdiv
    exact endpoint_observable_at (fun _ => 1) T z hwait k hk
  change (∫⁻ z,endpointObservable (fun _ => 1) T z ∂jointSourceTrajectory collect V r d hV hr hd X)=1
  rw [lintegral_congr_ae he]
  simp

end
end FiniteCopyReactor
