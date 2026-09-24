import proofs.RandomViability.ProductiveRAF
import proofs.RandomViability.ProductiveOperationProbability

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

def ProductiveRAFSuccess {n : ℕ} (c : SourceMoleculeFibreConfig n) (r : Reaction n)
    (V m : ℕ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) {r} ∧ ProductiveOperation r V m z

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem productive_raf_success_measurable (c : SourceMoleculeFibreConfig n) (r : Reaction n)
    (V m : ℕ) : MeasurableSet {z | ProductiveRAFSuccess c r V m z} := by
  by_cases hr : IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig c) {r}
  · simpa only [ProductiveRAFSuccess,hr,true_and] using productive_operation_measurable r V m
  · simp only [ProductiveRAFSuccess,hr,false_and,Set.setOf_false]
    exact MeasurableSet.empty

/-- The probability sandwich now explicitly requires a genuine internally
catalyzed RAF, not just a productive labelled path. -/
theorem source_productive_raf_bounds (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (a : ℝ) (ha : 1 < a)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r, productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon)
    (hc : ∀ r z, 4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16) :
    let p := sourceAverage a n (fun c =>
      (physicalTrajectoryLaw (by omega) c (V : NNReal) 1
        (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat (foodOnlyCounts n V)
        {z | ProductiveRAFSuccess c (productiveReaction hn) V ((V+9)/10) z}).toReal)
    productiveBeta V*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ≤ p ∧
    p ≤ (Fintype.card (Molecule (10*V))*Fintype.card (Reaction (10*V+2)) : ℕ)*
      (windowZipfMean a (sourceReactionCount n)/sourceReactionCount n) := by
  dsimp only
  constructor
  · apply sourceAverage_incidence_lower hn a ha (reactionProduct (productiveReaction hn))
      (productiveReaction hn) (productiveBeta V)
    · intro c
      exact ENNReal.toReal_nonneg
    · intro c hsel
      have hraf := productive_singleton_isRAF hn c hsel
      have hlow := concrete_productive_probability_lower hn V hV c basal cat hb hc hsel
      rw [← productive_realized_measure_eq hn V hV c basal cat] at hlow
      have hsub : productiveRealizedEvent hn V ⊆
          {z | ProductiveRAFSuccess c (productiveReaction hn) V ((V+9)/10) z} := by
        intro z hz
        exact ⟨hraf,productive_realized_operation hn V hV z hz⟩
      have hh := ENNReal.toReal_mono (measure_ne_top _ _) (hlow.trans (measure_mono hsub))
      simpa only [ENNReal.toReal_ofReal (productiveBeta_pos V hV).le] using hh
  · refine le_trans ?_ (source_productive_operation_bounds hn V hV a ha basal cat hb hc).2
    apply sourceAverage_mono a ha
    intro c
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (fun _ hz => hz.2)

end
end RandomViability
