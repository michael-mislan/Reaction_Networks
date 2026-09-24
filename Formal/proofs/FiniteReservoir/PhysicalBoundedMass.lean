import proofs.FiniteReservoir.PhysicalKilledProducts
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic

namespace FiniteReservoir
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding Filter
open scoped ENNReal Topology
noncomputable section
variable {M : ℕ}
open FiniteCopyReactor (reactorFood reactorTrajectoryFood)
set_option maxHeartbeats 30000

def boundedMassBeforeTime (B : ℕ) (T : ℝ)
    (z : ℕ → JumpState (CountState M) CompetitionChannel) : Prop :=
  (∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ T) ∧ ∀ k, massRegion B (z k).1

theorem bounded_mass_before_time_null (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) (B : ℕ) (T : ℝ) :
    reactorTrajectory M p V hV N {z | boundedMassBeforeTime B T z} = 0 := by
  obtain ⟨q, hq, hb⟩ := physical_killed_product_bound M p V hV N B
  let a := ENNReal.ofReal (Real.exp (-T))
  let ρ := ENNReal.ofReal (q/(q+1))
  have hρ : ρ < 1 := by
    dsimp [ρ]
    rw [ENNReal.ofReal_lt_one]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hbound : ∀ K, a*reactorTrajectory M p V hV N
      {z | boundedMassBeforeTime B T z} ≤ ρ^K := by
    intro K
    have hp' := (prefixProduct_measurable (massKilledMultiplier (M := M) B)
      (massKilledMultiplier_measurable (M := M) B) K).comp
      (Preorder.measurable_frestrictLe (X := fun _ : ℕ => JumpState (CountState M) CompetitionChannel) K)
    have hp : Measurable (trajectoryProduct (massKilledMultiplier (M := M) B) K) := by
      simpa only [Function.comp_def, prefixProduct_restrict] using hp'
    have hsub : {z : ℕ → JumpState (CountState M) CompetitionChannel | boundedMassBeforeTime B T z} ⊆
        {z | a ≤ trajectoryProduct (massKilledMultiplier (M := M) B) K z} := by
      intro z hz
      exact massKilledProduct_lower B K T z (fun i _ => hz.2 i) (hz.1 K)
    exact (mul_le_mul_right (measure_mono hsub) a).trans
      ((mul_meas_ge_le_lintegral hp a).trans (hb K))
  have hz : a*reactorTrajectory M p V hV N
      {z | boundedMassBeforeTime B T z} = 0 := by
    apply le_antisymm ?_ (by positivity)
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) (Eventually.of_forall hbound)
  have ha : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  exact (mul_eq_zero.mp hz).resolve_left ha

end
end FiniteReservoir
