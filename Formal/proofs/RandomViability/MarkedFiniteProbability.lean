import proofs.RandomViability.MarkedFiniteEvent

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_finite_marked_success_lower (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (N : Molecule n → ℕ)
    (hinitM : (countMass N : ℝ)/V ≤ 10)
    (hinitL : (N (reactionLeft r) : ℝ)/V = 1)
    (hinitR : (N (reactionRight r) : ℝ)/V = 1)
    (hinitP : (N (reactionProduct r) : ℝ)/V = 0)
    (hscale : 2*(n : ℝ)/markedNoiseDelta ≤ (V : ℝ)) :
    1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) ≤
      (physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
        {z | finiteMarkedSuccess V r z}).toReal := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  have hw := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat)
  have hsub : ∀ᵐ z ∂μ,z ∈ {z | ¬finiteMarkedSuccess V r z} → z ∈ {z | ¬markedProductiveCoverage V r 101 z} := by
    filter_upwards [hw] with z hz
    intro hbad hgood
    exact hbad (marked_coverage_implies_finite V r z hz hgood)
  have ht := (measure_mono_ae hsub).trans (physical_marked_productive_uniform_tail hn c V hV basal cat
    hb hcatCap hfood r hl hr hlen huw huz hwz hsel hbas hcat N hinitM hinitL hinitR hinitP hscale)
  have hb' : (μ {z | ¬finiteMarkedSuccess V r z}).toReal ≤
      24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) := by
    have hh := ENNReal.toReal_mono (by finiteness) ht
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh
  have he := probReal_add_probReal_compl (μ := μ) (finite_marked_success_measurable V r)
  change (μ {z | finiteMarkedSuccess V r z}).toReal+(μ {z | ¬finiteMarkedSuccess V r z}).toReal = 1 at he
  change 1-24*Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ))) ≤ (μ {z | finiteMarkedSuccess V r z}).toReal
  linarith only [he,hb']

end
end RandomViability
