import proofs.RandomViability.MarkedCatalyticUpper
import proofs.RandomViability.CollectiveSourceLower

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

/-- A fixed finite constant. Never numerically expand this catalog cardinality. -/
def collectiveSourceUpperConstant : ℝ :=
  (Fintype.card (Molecule collectiveUpperCutoff)*Fintype.card (Reaction (collectiveUpperCutoff+2)) : ℕ)

theorem food_only_nonfood_zero (n V : ℕ) : countNonfoodMass (foodOnlyCounts n V) = 0 := by
  apply Finset.sum_eq_zero
  intro q _
  dsimp only
  by_cases hq : q ∈ binaryFood n 2
  · have hl := (Finset.mem_filter.mp hq).2
    simp [foodMassWeight,hl]
  · simp [foodOnlyCounts,hq]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem source_collective_success_upper (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hc : ∀ r z,(cat r z : ℝ) ≤ 16) :
    sourceAverage a n (fun c =>
      (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
        (by exact_mod_cast hV) (by norm_num) basal cat (foodOnlyCounts n V)
        {z | finiteMarkedSuccess (V : NNReal) (productiveReaction hn) z}).toReal) ≤
      collectiveSourceUpperConstant*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
        2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  let f := fun c : SourceMoleculeFibreConfig n =>
    (physicalTrajectoryLaw (by omega : 2 ≤ n) c (V : NNReal) 1
      (by exact_mod_cast hV) (by norm_num) basal cat (foodOnlyCounts n V)
      {z | finiteMarkedSuccess (V : NNReal) (productiveReaction hn) z}).toReal
  have hp : ∀ c,f c ≤ 1 := fun _ => measureReal_le_one
  have hg : ∀ c,¬ShortIncidence collectiveUpperCutoff c →
      f c ≤ 2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
    intro c hgood
    exact physical_collective_upper_without_short_incidence hn c hgood (V : NNReal)
      (by exact_mod_cast hV) hscale basal cat hb hc (foodOnlyCounts n V)
      (food_only_nonfood_zero n V) (productiveReaction hn)
  have h := sourceAverage_le_bad_add a n ha hn (ShortIncidence collectiveUpperCutoff) f
    (2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) (by positivity) hp hg
  exact h.trans (add_le_add (shortIncidence_mass_le a n collectiveUpperCutoff ha hn) le_rfl)

theorem fully_averaged_collective_upper (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a) :
    fullyAveragedCollectiveProbability hn V hV a ≤
      collectiveSourceUpperConstant*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
        2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
  have hcard : (0 : ℝ) < Fintype.card (KineticMarkConfig n) := by exact_mod_cast Fintype.card_pos
  unfold fullyAveragedCollectiveProbability uniformFiniteAverage
  rw [div_le_iff₀ hcard]
  calc
    _ ≤ ∑ _u : KineticMarkConfig n,
        (collectiveSourceUpperConstant*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
          2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) := by
      apply Finset.sum_le_sum
      intro u _
      apply source_collective_success_upper hn V hV hscale a ha (kineticBasal u) (kineticCatalytic u)
      · intro r
        have hb := (kinetic_basal_bounds u r).2
        norm_num [productiveEpsilon] at hb
        linarith only [hb]
      · exact fun r z => (kinetic_catalytic_bounds u r z).2
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem fully_averaged_collective_bounds (hn : 4 ≤ n) (V : ℕ) (hV : 0 < V)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) (a : ℝ) (ha : 1 < a) :
    (sourceEmptyRowMass a n ^ 6*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1)*
      (1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) ≤
        fullyAveragedCollectiveProbability hn V hV a ∧
    fullyAveragedCollectiveProbability hn V hV a ≤
      collectiveSourceUpperConstant*(windowZipfMean a (sourceReactionCount n)/sourceReactionCount n)+
        2*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) :=
  ⟨fully_averaged_collective_lower hn V hV hscale a ha,
    fully_averaged_collective_upper hn V hV hscale a ha⟩

end
end RandomViability
