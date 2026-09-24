import proofs.FiniteCopyReactor.CountFoodCrossing
import Mathlib.Analysis.SpecificLimits.Basic

namespace FiniteCopyReactor
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 30000

theorem geometric_ofReal_tendsto_zero (C : ℝ) :
    Tendsto (fun b : ℕ => ENNReal.ofReal (C/(2 : ℝ)^b)) atTop (𝓝 0) := by
  have hr : Tendsto (fun b : ℕ => C/(2 : ℝ)^b) atTop (𝓝 0) := by
    simpa only [one_div_pow, mul_one_div, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).const_mul C
  simpa only [ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hr

def unboundedFoodBeforeTime (T : ℝ)
    (z : ℕ → JumpState Counts CompetitionChannel) : Prop :=
  (∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ T) ∧
    ∀ b, ∃ j, b ≤ incomingSum (fun i => reactorTrajectoryFood (z (i+1)).2.1) j

theorem unbounded_food_before_time_null (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) (T : ℝ) :
    reactorTrajectory V r d hV hr hd N {z | unboundedFoodBeforeTime T z} = 0 := by
  have hsub : ∀ b, {z : ℕ → JumpState Counts CompetitionChannel |
      unboundedFoodBeforeTime T z} ⊆ foodCrossingEvent b T := by
    intro b z hz
    obtain ⟨ht, hf⟩ := hz
    have hex := hf b
    let j := Nat.find hex
    have hj : b ≤ incomingSum (fun i => reactorTrajectoryFood (z (i+1)).2.1) j := Nat.find_spec hex
    have hbefore : ∀ i < j, incomingSum (fun l => reactorTrajectoryFood (z (l+1)).2.1) i < b := by
      intro i hi
      exact lt_of_not_ge (Nat.find_min hex hi)
    exact Set.mem_iUnion.mpr ⟨j, j, le_rfl, hbefore, hj, ht j⟩
  have hb : ∀ b, reactorTrajectory V r d hV hr hd N {z | unboundedFoodBeforeTime T z} ≤
      ENNReal.ofReal (Real.exp ((2*V)*T)/(2 : ℝ)^b) := fun b =>
    (measure_mono (hsub b)).trans (food_crossing_any_jump_probability V r d hV hr hd N b T)
  apply le_antisymm ?_ (by positivity)
  exact ge_of_tendsto (geometric_ofReal_tendsto_zero (Real.exp ((2*V)*T)))
    (Eventually.of_forall hb)

end
end FiniteCopyReactor
