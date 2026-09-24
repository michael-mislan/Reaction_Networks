import proofs.FiniteReservoir.PhysicalUnboundedFood
import proofs.FiniteReservoir.PhysicalBoundedMass
import proofs.RandomViability.JumpWaitingSupport

namespace FiniteReservoir
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding Filter
open scoped ENNReal Topology
noncomputable section
variable {M : ℕ}
open FiniteCopyReactor (reactorFood reactorTrajectoryFood)
set_option maxHeartbeats 30000

def physicalTimeBounded (T : ℝ)
    (z : ℕ → JumpState (CountState M) CompetitionChannel) : Prop :=
  ∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ T

theorem physical_bounded_time_null (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) (T : ℝ) :
    reactorTrajectory M p V hV N {z | physicalTimeBounded T z} = 0 := by
  have hf : ∀ᵐ z ∂reactorTrajectory M p V hV N, ¬unboundedFoodBeforeTime T z :=
    (measure_eq_zero_iff_ae_notMem).mp (unbounded_food_before_time_null M p V hV N T)
  have hb : ∀ᵐ z ∂reactorTrajectory M p V hV N, ∀ B, ¬boundedMassBeforeTime B T z := by
    apply ae_all_iff.mpr
    intro B
    exact (measure_eq_zero_iff_ae_notMem).mp (bounded_mass_before_time_null M p V hV N B T)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf, hb, reactor_mass_envelope M p V hV N] with z hzfood hzbound hmass
  intro htime
  have hnot : ¬∀ b, ∃ j, b ≤ incomingSum (fun i => reactorTrajectoryFood (z (i+1)).2.1) j :=
    fun h => hzfood ⟨htime, h⟩
  push Not at hnot
  obtain ⟨b, hb⟩ := hnot
  apply hzbound (reactorMass N+b)
  refine ⟨htime, ?_⟩
  intro k
  exact (hmass k).trans (Nat.add_le_add_left (Nat.le_of_lt (hb k)) (reactorMass N))

theorem physical_jump_times_tendsto_atTop (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) :
    ∀ᵐ z ∂reactorTrajectory M p V hV N,
      Tendsto (waitingSum (fun i => (z (i+1)).2.2)) atTop atTop := by
  have hb : ∀ᵐ z ∂reactorTrajectory M p V hV N,
      ∀ L : ℕ, ¬physicalTimeBounded (L : ℝ) z := by
    apply ae_all_iff.mpr
    intro L
    exact (measure_eq_zero_iff_ae_notMem).mp (physical_bounded_time_null M p V hV N L)
  have hw := jumpTrajectory_wait_nonneg N reactorNext (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)
  filter_upwards [hb, hw] with z hz hwait
  have hm : Monotone (waitingSum (fun i => (z (i+1)).2.2)) := by
    apply monotone_nat_of_le_succ
    intro k
    change (∑ i ∈ Finset.range k, (z (i+1)).2.2) ≤ ∑ i ∈ Finset.range (k+1), (z (i+1)).2.2
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hwait k)
  apply (tendsto_atTop_atTop_iff_of_monotone hm).mpr
  intro T
  obtain ⟨M, hM⟩ := exists_nat_gt T
  have hnot : ¬∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ (M : ℝ) := hz M
  push Not at hnot
  obtain ⟨k, hk⟩ := hnot
  exact ⟨k, hM.le.trans hk.le⟩

end
end FiniteReservoir
