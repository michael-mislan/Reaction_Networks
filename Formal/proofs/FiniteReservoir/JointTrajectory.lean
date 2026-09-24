import proofs.FiniteReservoir.JointCountSource
import proofs.FiniteCopyReactor.JumpProjection
import proofs.FiniteReservoir.ActualSource

namespace FiniteReservoir
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding Filter FiniteCopyReactor
open scoped ENNReal Topology

def jointSourceTrajectory (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M) (hV : 0 < V) 
    (X : JointCounts M) : Measure (ℕ → JumpState (JointCounts M) CompetitionChannel) :=
  jumpTrajectoryLaw X (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (joint_reactor_total_pos V M p hV)

instance jointSourceTrajectory_probability (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M)
    (hV : 0 < V)  (X : JointCounts M) :
    IsProbabilityMeasure (jointSourceTrajectory collect V M p hV X) := by
  unfold jointSourceTrajectory
  infer_instance

/-- Erasing counters recovers the exact augmented count trajectory, including all waits and labels. -/
theorem joint_trajectory_projection (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M)
    (hV : 0 < V)  (X : JointCounts M) :
    (jointSourceTrajectory collect V M p hV X).map (projectJumpPath (fun Y : JointCounts M => Y.1))=
      reactorTrajectory M p V hV X.1 :=
  project_jump_trajectory (fun Y : JointCounts M => Y.1) measurable_fst
    (jointReactorNext collect) reactorNext (fun _ _ => rfl) (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV) X

theorem joint_trajectory_nonexplosion (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M)
    (hV : 0 < V)  (X : JointCounts M) :
    ∀ᵐ z ∂jointSourceTrajectory collect V M p hV X,Tendsto (jumpElapsed z) atTop atTop := by
  have hp : ∀ᵐ z ∂(jointSourceTrajectory collect V M p hV X).map
      (projectJumpPath (fun Y : JointCounts M => Y.1)),Tendsto (jumpElapsed z) atTop atTop := by
    rw [joint_trajectory_projection]
    exact physical_jump_times_tendsto_atTop M p V hV X.1
  exact ae_of_ae_map (project_jump_path_measurable (fun Y : JointCounts M => Y.1) measurable_fst).aemeasurable hp

/-- Counters do not change the physical process and record exactly the literal event marks. -/
theorem joint_actual_events (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M)
    (hV : 0 < V)  (X : JointCounts M) :
    ∀ᵐ z ∂jointSourceTrajectory collect V M p hV X,∀ k,∃ j : CompetitionChannel,
      (z (k+1)).2.1=Sum.inr j ∧
      0 < rate (countState (z k).1.1) V p.release p.cleavage p.capacity j ∧
      (∀ i,reactants (competitionBase j) i ≤ (z k).1.1.1 i) ∧
      countState (z (k+1)).1.1=next (countState (z k).1.1) j ∧
      ∀ i,(z (k+1)).1.2 i=(z k).1.2 i+integerCycleMarks collect j i := by
  have hp := actual_source_events M p V hV X.1
  rw [← joint_trajectory_projection collect V M p hV X] at hp
  have hh := ae_of_ae_map (project_jump_path_measurable (fun Y : JointCounts M => Y.1) measurable_fst).aemeasurable hp
  have hc := jumpTrajectory_consistent X (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (joint_reactor_total_pos V M p hV)
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

theorem joint_source_endpoint_one (collect : Bool) (V : ℝ) (M : ℕ) (p : Parameters M)
    (hV : 0 < V)  (X : JointCounts M) (T : ℝ) (hT : 0 ≤ T) :
    jointSourceEndpoint collect V M p hV (fun _ => 1) X T=1 := by
  have hw := jumpTrajectory_wait_nonneg X (jointReactorNext collect) (jointReactorRate V M p)
    (joint_reactor_nonneg V M p hV) (joint_reactor_total_pos V M p hV)
  have hn := joint_trajectory_nonexplosion collect V M p hV X
  have he : ∀ᵐ z ∂jointSourceTrajectory collect V M p hV X,endpointObservable (fun _ => 1) T z=1 := by
    filter_upwards [hw,hn] with z hwait hdiv
    obtain ⟨k,hk⟩ := endpoint_interval_exists z T hT hdiv
    exact endpoint_observable_at (fun _ => 1) T z hwait k hk
  change (∫⁻ z,endpointObservable (fun _ => 1) T z ∂jointSourceTrajectory collect V M p hV X)=1
  rw [lintegral_congr_ae he]
  simp

end
end FiniteReservoir
