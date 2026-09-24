import proofs.RandomViability.MarkedOutputProbability

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def markedNoiseDelta : ℝ := 1/600000000000000000000
def markedNoiseRate : ℝ := markedNoiseDelta^2/40000000

theorem marked_noise_rate_pos : 0 < markedNoiseRate := by norm_num [markedNoiseRate,markedNoiseDelta]

theorem marked_noise_margins (n V : ℝ) (hn : 4 ≤ n) (hV : 0 < V)
    (hscale : 2*n/markedNoiseDelta ≤ V) :
    markedNoiseDelta+n/V ≤ 1/8 ∧ markedNoiseDelta+2/V ≤ 1/80 ∧
    markedNoiseDelta+2/V ≤ 1/100000 ∧ markedNoiseDelta+2/V ≤ 1/300000000000000000000 ∧
    markedNoiseDelta+n/V ≤ 1/40 ∧ markedNoiseDelta+n/V ≤ 1/100 := by
  have hd : 0 < markedNoiseDelta := by norm_num [markedNoiseDelta]
  have hmul := (div_le_iff₀ hd).1 hscale
  have hnv : n/V ≤ markedNoiseDelta/2 := (div_le_iff₀ hV).2 (by nlinarith only [hmul])
  have h2v : 2/V ≤ markedNoiseDelta/2 :=
    (div_le_div_of_nonneg_right (by linarith only [hn] : (2 : ℝ) ≤ n) hV.le).trans hnv
  norm_num [markedNoiseDelta] at hnv h2v ⊢
  constructor
  · linarith only [hnv]
  constructor
  · linarith only [h2v]
  constructor
  · linarith only [h2v]
  constructor
  · linarith only [h2v]
  constructor <;> linarith only [hnv]

theorem marked_noise_exponents (n V : ℝ) (hn : 4 ≤ n) (hV : 0 < V) :
    markedNoiseRate*V/n ≤ markedNoiseDelta^2*V/(4*n*(96011*101+markedNoiseDelta)) ∧
    markedNoiseRate*V/n ≤ markedNoiseDelta^2*V/(4*(96000*101+2*markedNoiseDelta)) := by
  have hn0 : 0 < n := by linarith only [hn]
  have hd : 0 < markedNoiseDelta := by norm_num [markedNoiseDelta]
  have hc : 4*(96011*(101 : ℝ)+markedNoiseDelta) ≤ 40000000 := by norm_num [markedNoiseDelta]
  have he : markedNoiseRate*V/n = markedNoiseDelta^2*V/(40000000*n) := by
    unfold markedNoiseRate
    ring
  rw [he]
  constructor
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hc hn0.le]
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    norm_num [markedNoiseDelta] at *
    linarith only [hn]

theorem marked_six_terms_uniform (n V : ℝ) (hn : 4 ≤ n) (hV : 0 < V) :
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*n*(96011*101+markedNoiseDelta)))))+
    12*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*(96000*101+2*markedNoiseDelta)))))+
    4*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*(96000*101+2*markedNoiseDelta)))))+
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*(96000*101+2*markedNoiseDelta)))))+
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*n*(96011*101+markedNoiseDelta)))))+
    2*ENNReal.ofReal (Real.exp (-(markedNoiseDelta^2*V/(4*n*(96011*101+markedNoiseDelta))))) ≤
      24*ENNReal.ofReal (Real.exp (-(markedNoiseRate*V/n))) := by
  have h := marked_noise_exponents n V hn hV
  have hN := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg h.1))
  have hC := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg h.2))
  calc
    _ ≤ 2*ENNReal.ofReal (Real.exp (-(markedNoiseRate*V/n)))+
        12*ENNReal.ofReal (Real.exp (-(markedNoiseRate*V/n)))+
        4*ENNReal.ofReal (Real.exp (-(markedNoiseRate*V/n)))+
        2*ENNReal.ofReal (Real.exp (-(markedNoiseRate*V/n)))+
        2*ENNReal.ofReal (Real.exp (-(markedNoiseRate*V/n)))+
        2*ENNReal.ofReal (Real.exp (-(markedNoiseRate*V/n))) :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_right hN 2) (mul_le_mul_right hC 12))
        (mul_le_mul_right hC 4)) (mul_le_mul_right hC 2)) (mul_le_mul_right hN 2)) (mul_le_mul_right hN 2)
    _ = _ := by ring

end
end RandomViability
