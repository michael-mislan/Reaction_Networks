import proofs.StartupCount.SourceCountLaw
import proofs.StartupCount.EnvelopeTail

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

theorem weighted_power_tail (p : ℝ≥0∞) (m l : ℕ) (hl : l ≤ m)
    (hb : ENNReal.ofReal ((9/10 : ℝ)^l)*p ≤ ENNReal.ofReal (10*(9/10 : ℝ)^m)) :
    p ≤ ENNReal.ofReal (10*(9/10 : ℝ)^(m-l)) := by
  have hq : 0 < (9/10 : ℝ)^l := by positivity
  have hd : p ≤ ENNReal.ofReal (10*(9/10 : ℝ)^m)/ENNReal.ofReal ((9/10 : ℝ)^l) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hq)))
      (Or.inl ENNReal.ofReal_ne_top)).mpr
    simpa only [mul_comm] using hb
  rw [← ENNReal.ofReal_div_of_pos hq] at hd
  have he : (10*(9/10 : ℝ)^m)/(9/10 : ℝ)^l = 10*(9/10 : ℝ)^(m-l) := by
    rw [pow_sub₀ (9/10 : ℝ) (by norm_num) hl]
    ring
  rwa [he] at hd

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem source_count_tail (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → cfg z = ∅)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hbas : (1/500000000 : ℝ) ≤ basal r)
    (m : ℕ) (hm : 10 ≤ m) (hmV : (m : ℝ) ≤ (V : ℝ)/2000000000000000000)
    (T : ℝ) (hT : 1 ≤ T) (N₀ : Molecule n → ℕ) (l : ℕ) (hl : l ≤ m) :
    physicalTrajectoryLaw hn cfg V 1 hV (by norm_num) basal cat N₀
      (guardedLowEvent (countGuard V r) (fun N => N (reactionProduct r)) l T) ≤
      ENNReal.ofReal (10*(9/10 : ℝ)^(m-l)) := by
  apply weighted_power_tail _ m l hl
  exact (source_count_low_event_bound hn cfg V hV basal cat r hb hc hfood hlen huw huz hwz
    hbas m hm hmV T (by linarith) N₀ l).trans (ENNReal.ofReal_le_ofReal
      (affine_source_envelope_le V T hV hT m (N₀ (reactionProduct r)) hmV))

end
end StartupCount
