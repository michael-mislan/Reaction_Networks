import proofs.FiniteCopyReactor.CountUnboundedFood
import proofs.FiniteReservoir.PhysicalFoodCrossing
import Mathlib.Analysis.SpecificLimits.Basic

namespace FiniteReservoir
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding Filter
open scoped ENNReal Topology
noncomputable section
variable {M : ℕ}
open FiniteCopyReactor (geometric_ofReal_tendsto_zero)
open FiniteCopyReactor (reactorFood reactorTrajectoryFood)
set_option maxHeartbeats 30000

def unboundedFoodBeforeTime (T : ℝ)
    (z : ℕ → JumpState (CountState M) CompetitionChannel) : Prop :=
  (∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ T) ∧
    ∀ b, ∃ j, b ≤ incomingSum (fun i => reactorTrajectoryFood (z (i+1)).2.1) j

theorem unbounded_food_before_time_null (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) (T : ℝ) :
    reactorTrajectory M p V hV N {z | unboundedFoodBeforeTime T z} = 0 := by
  have hsub : ∀ b, {z : ℕ → JumpState (CountState M) CompetitionChannel |
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
  have hb : ∀ b, reactorTrajectory M p V hV N {z | unboundedFoodBeforeTime T z} ≤
      ENNReal.ofReal (Real.exp ((2*V)*T)/(2 : ℝ)^b) := fun b =>
    (measure_mono (hsub b)).trans (food_crossing_any_jump_probability M p V hV N b T)
  apply le_antisymm ?_ (by positivity)
  exact ge_of_tendsto (geometric_ofReal_tendsto_zero (Real.exp ((2*V)*T)))
    (Eventually.of_forall hb)

end
end FiniteReservoir
