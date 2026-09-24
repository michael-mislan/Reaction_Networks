import proofs.RandomViability.MarkedUniformScale

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_marked_productive_uniform_tail (hn : 4 ≤ n)
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
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬markedProductiveCoverage V r 101 z} ≤
      24*ENNReal.ofReal (Real.exp (-(markedNoiseRate*(V : ℝ)/(n : ℝ)))) := by
  have hmargin := marked_noise_margins (n : ℝ) V (by exact_mod_cast hn) hV hscale
  have hd : 0 < markedNoiseDelta := by norm_num [markedNoiseDelta]
  exact (physical_marked_productive_failure_tail hn c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat 101 (by norm_num) N hinitM hinitL hinitR hinitP
    markedNoiseDelta markedNoiseDelta markedNoiseDelta markedNoiseDelta markedNoiseDelta markedNoiseDelta
    hd hd hd hd hd hd (by norm_num)
    hmargin.1 hmargin.2.1 hmargin.2.2.1 hmargin.2.2.2.1 hmargin.2.2.2.2.1 hmargin.2.2.2.2.2).trans
      (marked_six_terms_uniform (n : ℝ) V (by exact_mod_cast hn) hV)

end
end RandomViability
