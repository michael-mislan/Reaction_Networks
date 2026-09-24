import proofs.RandomViability.PhysicalKilledProducts
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy Filter
open scoped ENNReal Topology
noncomputable section
set_option maxHeartbeats 30000

def boundedMassBeforeTime {n : ℕ} (B : ℕ) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  (∀ k, waitingSum (fun i => (z (i+1)).2.2) k ≤ T) ∧ ∀ k, massRegion B (z k).1

theorem bounded_mass_before_time_null {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
    [MeasurableSingletonClass (PhysicalCountChannel n)] (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (hD : 0 < (D : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (B : ℕ) (T : ℝ) :
    physicalTrajectoryLaw hn c V D hV hD basal cat N {z | boundedMassBeforeTime B T z} = 0 := by
  obtain ⟨q, hq, hb⟩ := physical_killed_product_bound hn c V D hV hD basal cat N B
  let a := ENNReal.ofReal (Real.exp (-T))
  let ρ := ENNReal.ofReal ((q : ℝ)/(q+1))
  have hρ : ρ < 1 := by
    dsimp [ρ]
    rw [ENNReal.ofReal_lt_one]
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hbound : ∀ K, a*physicalTrajectoryLaw hn c V D hV hD basal cat N
      {z | boundedMassBeforeTime B T z} ≤ ρ^K := by
    intro K
    have hp' := (prefixProduct_measurable (massKilledMultiplier (n := n) B)
      (massKilledMultiplier_measurable (n := n) B) K).comp
      (Preorder.measurable_frestrictLe (X := fun _ : ℕ => JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) K)
    have hp : Measurable (trajectoryProduct (massKilledMultiplier (n := n) B) K) := by
      simpa only [Function.comp_def, prefixProduct_restrict] using hp'
    have hsub : {z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n) | boundedMassBeforeTime B T z} ⊆
        {z | a ≤ trajectoryProduct (massKilledMultiplier B) K z} := by
      intro z hz
      exact massKilledProduct_lower B K T z (fun i _ => hz.2 i) (hz.1 K)
    exact (mul_le_mul_right (measure_mono hsub) a).trans
      ((mul_meas_ge_le_lintegral hp a).trans (hb K))
  have hz : a*physicalTrajectoryLaw hn c V D hV hD basal cat N
      {z | boundedMassBeforeTime B T z} = 0 := by
    apply le_antisymm ?_ (by positivity)
    exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) (Eventually.of_forall hbound)
  have ha : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  exact (mul_eq_zero.mp hz).resolve_left ha

end
end RandomViability
