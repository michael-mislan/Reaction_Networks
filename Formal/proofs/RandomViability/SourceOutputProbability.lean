import proofs.RandomViability.PhysicalOutputProbability
import proofs.RandomViability.CollectiveRAFProbability

namespace RandomViability
open Classical MeasureTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 150000
local instance outputChannelSpace (n : ℕ) : MeasurableSpace (PhysicalCountChannel n) := ⊤
local instance outputChannelSingleton (n : ℕ) : MeasurableSingletonClass (PhysicalCountChannel n) := ⟨fun _ => trivial⟩

def anySourceRAF {n : ℕ} (c : SourceMoleculeFibreConfig n) : Prop :=
  ∃ Q : Finset (Reaction n),IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) Q

def averagedOutputProbability {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V) (a : ℝ)
    (A : SourceMoleculeFibreConfig n → Prop) (enabled : Bool := true) : ℝ :=
  uniformFiniteAverage (fun u : KineticMarkConfig n => sourceAverage a n (fun c =>
    if A c then (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
      (by exact_mod_cast hV) (by norm_num) (kineticBasal u)
      (if enabled then kineticCatalytic u else fun _ _ => 0) (foodOnlyCounts n V)
      {z | physicalOutputEvent (V : NNReal) z}).toReal else 0))

theorem source_average_const {n : ℕ} (hn : 4 ≤ n) (a : ℝ) (ha : 1 < a) (b : ℝ) :
    sourceAverage a n (fun _ => b) = b := by
  unfold sourceAverage
  rw [← Finset.sum_mul,sum_sourcePowerLawConfigWeight_eq_one a n ha hn,one_mul]

theorem averaged_output_bounds {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a)
    (A : SourceMoleculeFibreConfig n → Prop)
    (hA : ∀ c,sourceFoodSilentSeed (reactionProduct (productiveReaction hn)) (productiveReaction hn) c → A c) :
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
      (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) ≤ averagedOutputProbability hn V hV a A ∧
    averagedOutputProbability hn V hV a A ≤
      collectiveSourceUpperConstant*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
        4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  have hpoint (u : KineticMarkConfig n) :
      (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
        (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) ≤
      sourceAverage a n (fun c => if A c then
        (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1 (by exact_mod_cast hV) (by norm_num)
          (kineticBasal u) (kineticCatalytic u) (foodOnlyCounts n V) {z | physicalOutputEvent (V : NNReal) z}).toReal else 0) := by
    apply sourceAverage_food_silent_seed_lower hn a ha (reactionProduct (productiveReaction hn))
      (productive_reaction_food hn).2.2 (productiveReaction hn)
    · intro c
      split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
    · intro c hs
      rw [if_pos (hA c hs)]
      apply (concrete_collective_success_lower hn V hV hscale c (kineticBasal u) (kineticCatalytic u)
        (kinetic_basal_bounds u) (kinetic_catalytic_bounds u) hs).trans
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact measure_mono (fun z hz => finite_success_implies_output _ _ z hz)
  have hupper (u : KineticMarkConfig n) :
      sourceAverage a n (fun c => if A c then
        (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1 (by exact_mod_cast hV) (by norm_num)
          (kineticBasal u) (kineticCatalytic u) (foodOnlyCounts n V) {z | physicalOutputEvent (V : NNReal) z}).toReal else 0) ≤
      collectiveSourceUpperConstant*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
        4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
    apply le_trans (sourceAverage_le_bad_add a n ha hn (ShortIncidence collectiveUpperCutoff) _
      (4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) (by positivity) ?_ ?_)
      (add_le_add (shortIncidence_mass_le a n collectiveUpperCutoff ha hn) le_rfl)
    · intro c
      split_ifs
      · exact measureReal_le_one
      · norm_num
    · intro c hg
      split_ifs
      · exact physical_output_upper_without_short_incidence hn c hg (V : NNReal) (by exact_mod_cast hV)
          hscale (kineticBasal u) (kineticCatalytic u) (fun r => (kinetic_basal_bounds u r).2)
          (fun r z => (kinetic_catalytic_bounds u r z).2) (foodOnlyCounts n V) (food_only_nonfood_zero n V)
      · positivity
  unfold averagedOutputProbability uniformFiniteAverage
  simp only [if_true]
  constructor
  · rw [le_div_iff₀ hcard]
    calc
      _ = ∑ _u : KineticMarkConfig n, (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
          (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun u _ => hpoint u)
  · rw [div_le_iff₀ hcard]
    calc
      _ ≤ ∑ _u : KineticMarkConfig n, (collectiveSourceUpperConstant*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
          4*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) := Finset.sum_le_sum (fun u _ => hupper u)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem averaged_output_disabled_bound {n : ℕ} (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a) :
    averagedOutputProbability hn V hV a (fun _ => True) false ≤
      2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  unfold averagedOutputProbability uniformFiniteAverage
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [div_le_iff₀ hcard]
  calc
    _ ≤ ∑ _u : KineticMarkConfig n,2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
      apply Finset.sum_le_sum
      intro u _
      rw [← source_average_const hn a ha (2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))))]
      apply sourceAverage_mono a ha
      intro c
      exact physical_output_disabled_upper hn c (V : NNReal) (by exact_mod_cast hV) hscale
        (kineticBasal u) (fun r => (kinetic_basal_bounds u r).2) (foodOnlyCounts n V) (food_only_nonfood_zero n V)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end
end RandomViability
