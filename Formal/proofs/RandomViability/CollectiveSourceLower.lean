import proofs.RandomViability.MarkedFiniteProbability
import proofs.RandomViability.SourceFoodSilentSeed
import proofs.RandomViability.ProductiveKineticMarks

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem concrete_collective_success_lower (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ))
    (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon)
    (hc : ∀ r z,4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16)
    (hseed : sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn) c) :
    1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) ≤
      (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
        (by exact_mod_cast hV) (by norm_num) basal cat (foodOnlyCounts n V)
        {z | finiteMarkedSuccess (V : NNReal) (productiveReaction hn) z}).toReal := by
  have hVr : 0 < (V : ℝ) := by exact_mod_cast hV
  have hl := productive_reaction_lengths hn
  have hd := productive_reaction_distinct hn
  have hi := productive_initial_counts hn V
  apply physical_finite_marked_success_lower hn c (V : NNReal) (by exact_mod_cast hV) basal cat
    (fun r => (hb r).2) (fun r z => (hc r z).2) _ (productiveReaction hn)
    hl.1 hl.2.1 hl.2.2 hd.1 hd.2.1 hd.2.2 hseed.2 (hb _).1 (hc _ _).1
    (foodOnlyCounts n V) _ _ _ _ hscale
  · intro y hy
    exact hseed.1 y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩)
  · apply (div_le_iff₀ hVr).2
    exact_mod_cast food_only_count_mass_le (by omega : 2 ≤ n) V
  · rw [hi.1]
    exact div_self hVr.ne'
  · rw [hi.2.1]
    exact div_self hVr.ne'
  · rw [hi.2.2]
    simp

theorem source_collective_success_lower (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon)
    (hc : ∀ r z,4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16) :
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
      (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) ≤
      sourceAverage a n (fun c =>
        (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
          (by exact_mod_cast hV) (by norm_num) basal cat (foodOnlyCounts n V)
          {z | finiteMarkedSuccess (V : NNReal) (productiveReaction hn) z}).toReal) := by
  apply sourceAverage_food_silent_seed_lower hn a ha (reactionProduct (productiveReaction hn))
    (productive_reaction_food hn).2.2 (productiveReaction hn)
  · intro c
    exact ENNReal.toReal_nonneg
  · intro c hseed
    exact concrete_collective_success_lower hn V hV hscale c basal cat hb hc hseed

/-- Every source row, kinetic mark, and physical clock is averaged. -/
def fullyAveragedCollectiveProbability (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V) (a : ℝ) : ℝ :=
  uniformFiniteAverage (fun u : KineticMarkConfig n => sourceAverage a n (fun c =>
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
      (by exact_mod_cast hV) (by norm_num) (kineticBasal u) (kineticCatalytic u) (foodOnlyCounts n V)
      {z | finiteMarkedSuccess (V : NNReal) (productiveReaction hn) z}).toReal))

theorem fully_averaged_collective_lower (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a) :
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
      (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) ≤
      fullyAveragedCollectiveProbability hn V hV a := by
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  unfold fullyAveragedCollectiveProbability uniformFiniteAverage
  rw [le_div_iff₀ hcard]
  calc
    _ = ∑ _u : KineticMarkConfig n,
        (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
          (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun u _ => source_collective_success_lower hn V hV hscale a ha
      (kineticBasal u) (kineticCatalytic u) (kinetic_basal_bounds u) (kinetic_catalytic_bounds u))

end
end RandomViability
