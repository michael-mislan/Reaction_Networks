import proofs.RepeatedFunction.SourceLower
import proofs.RandomViability.SingletonDominance

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000
local instance missionChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance missionChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

def averagedMissionProbability {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V) (a : ℝ)
    (A : SourceMoleculeFibreConfig n → Prop) : ℝ :=
  uniformFiniteAverage (fun u : KineticMarkConfig n => sourceAverage a n (fun c =>
    if A c then (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
      (by exact_mod_cast hV) (by norm_num) (kineticBasal u) (kineticCatalytic u)
      (foodOnlyCounts n V) {z | twoWindowMission (V : NNReal) z}).toReal else 0))

theorem averaged_mission_nonneg {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (a : ℝ) (ha : 1 < a) (A : SourceMoleculeFibreConfig n → Prop) :
    0 ≤ averagedMissionProbability hn V hV a A := by
  unfold averagedMissionProbability uniformFiniteAverage sourceAverage
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (sourcePowerLawConfigWeight_nonneg a n ha c)
  dsimp only
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem averaged_mission_le_output {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (a : ℝ) (ha : 1 < a) (A : SourceMoleculeFibreConfig n → Prop) :
    averagedMissionProbability hn V hV a A ≤ averagedOutputProbability hn V hV a A := by
  unfold averagedMissionProbability averagedOutputProbability uniformFiniteAverage
  simp only [if_true]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro u _
  apply sourceAverage_mono a ha
  intro c
  split_ifs
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (fun z hz => two_window_implies_old_output _ z hz)
  · exact le_rfl

theorem averaged_mission_lower {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a)
    (A : SourceMoleculeFibreConfig n → Prop)
    (hA : ∀ c,sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn) c → A c) :
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
      (1-24*Real.exp (-(twoWindowNoiseRate*(V : ℝ)/(n : ℝ)))) ≤
      averagedMissionProbability hn V hV a A := by
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  unfold averagedMissionProbability uniformFiniteAverage
  rw [le_div_iff₀ hcard]
  calc
    _ = ∑ _u : KineticMarkConfig n,
        (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
        (1-24*Real.exp (-(twoWindowNoiseRate*(V : ℝ)/(n : ℝ)))) := by simp [mul_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u _
      apply sourceAverage_food_silent_seed_lower hn a ha (reactionProduct (productiveReaction hn))
        (productive_reaction_food hn).2.2 (productiveReaction hn)
      · intro c
        split_ifs
        · exact ENNReal.toReal_nonneg
        · exact le_rfl
      · intro c hs
        rw [if_pos (hA c hs)]
        exact concrete_two_window_success_lower hn V hV hscale c (kineticBasal u)
          (kineticCatalytic u) (kinetic_basal_bounds u) (kinetic_catalytic_bounds u) hs

theorem averaged_mission_without_singleton_upper {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (hsmall : (n : ℝ)/(V : ℝ) ≤ 1/200000)
    (a : ℝ) (ha : 1 < a) :
    averagedMissionProbability hn V hV a noProductiveSingleton ≤
      eventMass a n (fun c => ¬AtMostOneLocalIncidence singleIncidenceCutoff c)+
        localOutputNoiseUpper n (V : NNReal) :=
  (averaged_mission_le_output hn V hV a ha _).trans
    (averaged_output_without_singleton_upper hn V hV hscale hsmall a ha)

end
end RandomViability
