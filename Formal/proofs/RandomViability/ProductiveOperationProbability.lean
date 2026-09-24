import proofs.RandomViability.ProductiveOperationMeasurable
import proofs.RandomViability.SourceOccupiedBound

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem productive_operation_firing {n : ℕ} (r : Reaction n) (V m : ℕ) (hm : 0 < m)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hz : ProductiveOperation r V m z) : boundedCatalyticFiring (10*V) z := by
  have hout := hz.2.2.2.1
  have hex : ∃ i : ℕ,
      (if 1 < productiveClock (fun j => (z (j+1)).2.2) (i+1) ∧
        productiveClock (fun j => (z (j+1)).2.2) (i+1) ≤ 100
        then targetSignedCatalytic r (z (i+1)).2.1 else 0) ≠ 0 := by
    by_contra hh
    push Not at hh
    have he : operatingMarkedSum (targetSignedCatalytic r) z = 0 := by
      unfold operatingMarkedSum
      simp only [hh, tsum_zero]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  obtain ⟨i,hi⟩ := hex
  have hclock : 1 < productiveClock (fun j => (z (j+1)).2.2) (i+1) ∧
      productiveClock (fun j => (z (j+1)).2.2) (i+1) ≤ 100 := by
    by_contra hh
    simp [hh] at hi
  rw [if_pos hclock] at hi
  have hmono := productive_clock_monotone _ hz.1
  have hmass := (hz.2.1 i ⟨(hmono (Nat.le_succ i)).trans hclock.2,hclock.1⟩).2.2.2.2
  by_cases hf : (z (i+1)).2.1 = .inr (.inr (.inr (r,reactionProduct r,true)))
  · exact ⟨i,r,reactionProduct r,true,hmass,hf⟩
  · have hb : (z (i+1)).2.1 = .inr (.inr (.inr (r,reactionProduct r,false))) := by
      by_contra hb
      simp [targetSignedCatalytic,hf,hb] at hi
    exact ⟨i,r,reactionProduct r,false,hmass,hb⟩

theorem sourceAverage_mono {n : ℕ} (a : ℝ) (ha : 1 < a)
    (f g : SourceMoleculeFibreConfig n → ℝ) (h : ∀ c, f c ≤ g c) :
    sourceAverage a n f ≤ sourceAverage a n g := by
  apply Finset.sum_le_sum
  intro c _
  exact mul_le_mul_of_nonneg_left (h c) (sourcePowerLawConfigWeight_nonneg a n ha c)

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Explicit unconditional finite-size sandwich for the actual operating
event, averaged over the full capped-Zipf source. -/
theorem source_productive_operation_bounds (hn : 4 ≤ n) (V : ℕ) (hV : 40 ≤ V)
    (a : ℝ) (ha : 1 < a)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r, productiveEpsilon ≤ (basal r : ℝ) ∧ (basal r : ℝ) ≤ 4*productiveEpsilon)
    (hc : ∀ r z, 4 ≤ (cat r z : ℝ) ∧ (cat r z : ℝ) ≤ 16) :
    let p := sourceAverage a n (fun c =>
      (physicalTrajectoryLaw (by omega) c (V : NNReal) 1
        (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat (foodOnlyCounts n V)
        {z | ProductiveOperation (productiveReaction hn) V ((V+9)/10) z}).toReal)
    productiveBeta V*powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ≤ p ∧
    p ≤ (Fintype.card (Molecule (10*V))*Fintype.card (Reaction (10*V+2)) : ℕ)*
      (windowZipfMean a (sourceReactionCount n)/sourceReactionCount n) := by
  dsimp only
  constructor
  · refine (source_realized_productive_lower hn V hV a ha basal cat hb hc).trans ?_
    apply sourceAverage_mono a ha
    intro c
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro z hz
    exact productive_realized_operation hn V hV z hz
  · refine le_trans ?_ (source_bounded_catalytic_firing_upper hn (10*V) a ha
      (V : NNReal) 1 (by exact_mod_cast (show 0 < V by omega)) (by norm_num) basal cat
      (foodOnlyCounts n V))
    apply sourceAverage_mono a ha
    intro c
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro z hz
    exact productive_operation_firing _ _ _ (productive_volume_rounding V hV).1 z hz

end
end RandomViability
