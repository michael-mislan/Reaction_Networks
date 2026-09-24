import proofs.RandomViability.UnboundedFoodNull
import proofs.RandomViability.BoundedMassNull
import proofs.RandomViability.JumpWaitingSupport

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 30000

def physicalTimeBounded {n : ℕ} (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ T

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_bounded_time_null (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (T : ℝ) :
    physicalTrajectoryLaw hn c V D hV hD basal cat N {z | physicalTimeBounded T z} = 0 := by
  have hf : ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N, ¬unboundedFoodBeforeTime T z :=
    (measure_eq_zero_iff_ae_notMem).mp (unbounded_food_before_time_null hn c V D hV hD basal cat N T)
  have hb : ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N, ∀ B, ¬boundedMassBeforeTime B T z := by
    apply ae_all_iff.mpr
    intro B
    exact (measure_eq_zero_iff_ae_notMem).mp (bounded_mass_before_time_null hn c V D hV hD basal cat N B T)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf, hb, physicalTrajectory_mass_from_initial hn c V D hV hD basal cat N] with z hzfood hzbound hmass
  intro htime
  have hnot : ¬∀ b, ∃ j, b ≤ incomingSum (fun i => trajectoryFoodInput (z (i+1)).2.1) j :=
    fun h => hzfood ⟨htime, h⟩
  push Not at hnot
  obtain ⟨b, hb⟩ := hnot
  apply hzbound (countMass N+b)
  refine ⟨htime, ?_⟩
  intro k
  exact (hmass k).trans (Nat.add_le_add_left (Nat.le_of_lt (hb k)) (countMass N))

theorem physical_jump_times_tendsto_atTop (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N,
      Tendsto (waitingSum (fun i => (z (i+1)).2.2)) atTop atTop := by
  have hb : ∀ᵐ z ∂physicalTrajectoryLaw hn c V D hV hD basal cat N,
      ∀ M : ℕ, ¬physicalTimeBounded (M : ℝ) z := by
    apply ae_all_iff.mpr
    intro M
    exact (measure_eq_zero_iff_ae_notMem).mp (physical_bounded_time_null hn c V D hV hD basal cat N M)
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext (unboundedPhysicalRate c V D basal cat)
    (unboundedPhysicalRate_nonneg c V D basal cat) (unbounded_total_pos hn c V D hV hD basal cat)
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
end RandomViability
