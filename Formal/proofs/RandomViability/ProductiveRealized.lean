import proofs.RandomViability.SourceProductiveLower
import proofs.RandomViability.JumpWaitingSupport
import proofs.RandomViability.ProductiveEndpoints
import proofs.RandomViability.ProductiveBasalBudget

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

/-- A measurable productive cylinder with its almost-sure chronological support. -/
def productiveRealizedEvent {n : ℕ} (hn : 4 ≤ n) (V : ℕ) :
    Set (ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :=
  {z | ∀ i, 0 ≤ (z (i+1)).2.2} ∩ productiveCylinderEvent hn V

variable {n : ℕ} [mCh : MeasurableSpace (PhysicalCountChannel n)]
  [sCh : MeasurableSingletonClass (PhysicalCountChannel n)]

theorem productive_realized_measurable (hn : 4 ≤ n) (V : ℕ) :
    MeasurableSet (productiveRealizedEvent hn V) := by
  apply MeasurableSet.inter ?_ (prescribed_cylinder_measurable _ _ _ _ _)
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const
    (measurable_pi_apply (i+1)).snd.snd)

theorem productive_realized_measure_eq (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (c : SourceMoleculeFibreConfig n)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) :
    physicalTrajectoryLaw (by omega) c (V : NNReal) 1
      (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat (foodOnlyCounts n V)
      (productiveRealizedEvent hn V) =
    physicalTrajectoryLaw (by omega) c (V : NNReal) 1
      (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat (foodOnlyCounts n V)
      (productiveCylinderEvent hn V) := by
  apply Measure.measure_inter_eq_of_ae
  exact jumpTrajectory_wait_nonneg _ _ _ _ _

/-- Source and trajectory randomness are both charged; retaining chronological
support does not cost any probability. -/
theorem source_realized_productive_lower (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (a : ℝ) (ha : 1 < a)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r, productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon)
    (hc : ∀ r z, 4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16) :
    productiveBeta V*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ≤
      sourceAverage a n (fun c =>
        (physicalTrajectoryLaw (by omega) c (V : NNReal) 1
          (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat (foodOnlyCounts n V)
          (productiveRealizedEvent hn V)).toReal) := by
  simp_rw [productive_realized_measure_eq hn V hV]
  exact source_concrete_productive_lower hn V hV a ha basal cat hb hc

end
end RandomViability
