import proofs.RepeatedFunction.MissionProbability

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def twoWindowNoiseRate : ℝ := markedNoiseDelta^2/80000000

theorem two_window_noise_rate_pos : 0 < twoWindowNoiseRate := by
  norm_num [twoWindowNoiseRate,markedNoiseDelta]

theorem two_window_noise_exponents (n V : ℝ) (hn : 4 ≤ n) (hV : 0 < V) :
    twoWindowNoiseRate*V/n ≤ markedNoiseDelta^2*V/(4*n*(96011*200+markedNoiseDelta)) ∧
    twoWindowNoiseRate*V/n ≤ markedNoiseDelta^2*V/(4*(96000*200+2*markedNoiseDelta)) := by
  have hn0 : 0 < n := by linarith only [hn]
  have hd : 0 < markedNoiseDelta := by norm_num [markedNoiseDelta]
  have hc : 4*(96011*(200 : ℝ)+markedNoiseDelta) ≤ 80000000 := by norm_num [markedNoiseDelta]
  have he : twoWindowNoiseRate*V/n = markedNoiseDelta^2*V/(80000000*n) := by
    unfold twoWindowNoiseRate
    ring
  rw [he]
  constructor
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hc hn0.le]
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    norm_num [markedNoiseDelta] at *
    linarith only [hn]

theorem two_window_six_terms_uniform (n V : ℝ) (hn : 4 ≤ n) (hV : 0 < V) :
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*n*(96011*200+markedNoiseDelta)))))+
    12*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*(96000*200+2*markedNoiseDelta)))))+
    4*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*(96000*200+2*markedNoiseDelta)))))+
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*(96000*200+2*markedNoiseDelta)))))+
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*n*(96011*200+markedNoiseDelta)))))+
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*n*(96011*200+markedNoiseDelta))))) ≤
      24*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*V/n))) := by
  have h := two_window_noise_exponents n V hn hV
  have hN := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg h.1))
  have hC := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg h.2))
  calc
    _ ≤ 2*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*V/n)))+
        12*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*V/n)))+
        4*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*V/n)))+
        2*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*V/n)))+
        2*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*V/n)))+
        2*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*V/n))) :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_right hN 2) (mul_le_mul_right hC 12))
        (mul_le_mul_right hC 4)) (mul_le_mul_right hC 2)) (mul_le_mul_right hN 2)) (mul_le_mul_right hN 2)
    _ = _ := by ring


variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_two_window_uniform_tail (hn : 4 ≤ n)
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
      {z | ¬twoWindowMission V z} ≤
      24*ENNReal.ofReal (Real.exp (-(twoWindowNoiseRate*(V : ℝ)/(n : ℝ)))) := by
  have hmargin := marked_noise_margins (n : ℝ) V (by exact_mod_cast hn) hV hscale
  have hd : 0 < markedNoiseDelta := by norm_num [markedNoiseDelta]
  exact (physical_two_window_failure_tail hn c V hV basal cat hb hcatCap hfood r
    hl hr hlen huw huz hwz hsel hbas hcat N hinitM hinitL hinitR hinitP
    markedNoiseDelta markedNoiseDelta markedNoiseDelta markedNoiseDelta markedNoiseDelta markedNoiseDelta
    hd hd hd hd hd hd
    hmargin.1 hmargin.2.1 hmargin.2.2.1 hmargin.2.2.2.1 hmargin.2.2.2.2.1 (hmargin.2.2.2.2.2.trans (by norm_num))).trans
      (two_window_six_terms_uniform (n : ℝ) V (by exact_mod_cast hn) hV)


end
end RandomViability
