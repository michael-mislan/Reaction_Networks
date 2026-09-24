import proofs.RandomViability.FoodCrossingProbability
import Mathlib.Analysis.SpecificLimits.Basic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
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

def unboundedFoodBeforeTime {n : ℕ} (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  (∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ T) ∧
    ∀ b, ∃ j, b ≤ incomingSum (fun i => trajectoryFoodInput (z (i+1)).2.1) j

theorem unbounded_food_before_time_null {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
    [MeasurableSingletonClass (PhysicalCountChannel n)] (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (T : ℝ) :
    physicalTrajectoryLaw hn c V D hV hD basal cat N {z | unboundedFoodBeforeTime T z} = 0 := by
  have hsub : ∀ b, {z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) |
      unboundedFoodBeforeTime T z} ⊆ foodCrossingEvent b T := by
    intro b z hz
    obtain ⟨ht, hf⟩ := hz
    have hex := hf b
    let j := Nat.find hex
    have hj : b ≤ incomingSum (fun i => trajectoryFoodInput (z (i+1)).2.1) j := Nat.find_spec hex
    have hbefore : ∀ i < j, incomingSum (fun l => trajectoryFoodInput (z (l+1)).2.1) i < b := by
      intro i hi
      exact lt_of_not_ge (Nat.find_min hex hi)
    exact Set.mem_iUnion.mpr ⟨j, j, le_rfl, hbefore, hj, ht j⟩
  have hb : ∀ b, physicalTrajectoryLaw hn c V D hV hD basal cat N {z | unboundedFoodBeforeTime T z} ≤
      ENNReal.ofReal (Real.exp ((14*(D : ℝ)*V)*T)/(2 : ℝ)^b) := fun b =>
    (measure_mono (hsub b)).trans (food_crossing_any_jump_probability hn c V D hV hD basal cat N b T)
  apply le_antisymm ?_ (by positivity)
  exact ge_of_tendsto (geometric_ofReal_tendsto_zero (Real.exp ((14*(D : ℝ)*V)*T)))
    (Eventually.of_forall hb)

end
end RandomViability
