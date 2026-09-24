import proofs.RandomViability.ProductiveConcrete
import proofs.RandomViability.SourceUptakeTail

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

theorem sourceAverage_incidence_lower {n : ℕ} (hn : 4 ≤ n) (a : ℝ) (ha : 1 < a)
    (x : Molecule n) (r : Reaction n) (b : ℝ) (f : SourceMoleculeFibreConfig n → ℝ)
    (hf : ∀ c, 0 ≤ f c) (hb : ∀ c, r ∈ c x → b ≤ f c) :
    b*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ≤ sourceAverage a n f := by
  calc
    _ = (∑ c : SourceMoleculeFibreConfig n,
        if r ∈ c x then sourcePowerLawConfigWeight a n c else 0)*b := by
      rw [source_single_incidence_mass_eq_gatewayHit a ha hn x r]
      ring
    _ = ∑ c : SourceMoleculeFibreConfig n,
        if r ∈ c x then sourcePowerLawConfigWeight a n c*b else 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    _ ≤ sourceAverage a n f := by
      apply Finset.sum_le_sum
      intro c _
      have hw := sourcePowerLawConfigWeight_nonneg a n ha c
      by_cases hc : r ∈ c x
      · rw [if_pos hc]
        exact mul_le_mul_of_nonneg_left (hb c hc) hw
      · rw [if_neg hc]
        exact mul_nonneg hw (hf c)

variable {n : ℕ} [mCh : MeasurableSpace (PhysicalCountChannel n)]
  [sCh : MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Unconditional source-averaged probability of the concrete food-only
productive cylinder, with the exact without-replacement incidence marginal. -/
theorem source_concrete_productive_lower (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (a : ℝ) (ha : 1 < a)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r, productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon)
    (hc : ∀ r z, 4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16) :
    productiveBeta V*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ≤
      sourceAverage a n (fun c =>
        (physicalTrajectoryLaw (by omega) c (V : NNReal) 1
          (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat (foodOnlyCounts n V)
          (productiveCylinderEvent hn V)).toReal) := by
  apply sourceAverage_incidence_lower hn a ha (reactionProduct (productiveReaction hn))
    (productiveReaction hn) (productiveBeta V)
  · intro c
    exact ENNReal.toReal_nonneg
  · intro c hsel
    have hh := concrete_productive_probability_lower hn V hV c basal cat hb hc hsel
    have hr := ENNReal.toReal_mono (measure_ne_top _ _) hh
    simpa only [ENNReal.toReal_ofReal (productiveBeta_pos V hV).le] using hr

end
end RandomViability
