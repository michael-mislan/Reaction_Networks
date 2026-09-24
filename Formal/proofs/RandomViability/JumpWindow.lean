import proofs.RandomViability.FirstChannelLaw

set_option maxHeartbeats 20000

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set
noncomputable section

theorem holding_window_scalar_lower (b q Q a d e : ℝ)
    (hq : 0 < q) (hQ : q ≤ Q) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hb : e ≤ b) :
    e*d*Real.exp (-Q*(a+d)) ≤
      b/q*(Real.exp (-q*a)-Real.exp (-q*(a+d))) := by
  have heq : Real.exp (-q*a) = Real.exp (-q*(a+d))*Real.exp (q*d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hex := Real.add_one_le_exp (q*d)
  have hm := mul_le_mul_of_nonneg_left
    (show q*d ≤ Real.exp (q*d)-1 by linarith)
    (Real.exp_pos (-q*(a+d))).le
  have hdiff : q*d*Real.exp (-q*(a+d)) ≤
      Real.exp (-q*a)-Real.exp (-q*(a+d)) := by rw [heq]; nlinarith only [hm]
  have hmul := mul_le_mul_of_nonneg_left hdiff
    (div_nonneg (he.trans hb) hq.le)
  have hcancel : b/q*(q*d*Real.exp (-q*(a+d))) = b*d*Real.exp (-q*(a+d)) := by
    field_simp
  rw [hcancel] at hmul
  have hexp : Real.exp (-Q*(a+d)) ≤ Real.exp (-q*(a+d)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbmul := mul_le_mul_of_nonneg_right hb hd
  have hfinal := mul_le_mul hbmul hexp (Real.exp_pos _).le (mul_nonneg (he.trans hb) hd)
  exact hfinal.trans hmul

theorem exponential_Ioc (q a d : ℝ) (hq : 0 < q) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    expMeasure q (Ioc a (a+d)) =
      ENNReal.ofReal (Real.exp (-q*a)-Real.exp (-q*(a+d))) := by
  letI := isProbabilityMeasure_expMeasure hq
  have hset : Ioc a (a+d) = Iic (a+d) \ Iic a := by
    ext t
    simp only [mem_Ioc, mem_diff, mem_Iic, not_le]
    tauto
  rw [hset, measure_diff (Iic_subset_Iic.mpr (by linarith))
    measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _),
    exponential_Iic q (a+d) hq (by linarith), exponential_Iic q a hq ha]
  have hn : 0 ≤ 1-Real.exp (-q*a) := by
    have h := Real.exp_le_one_iff.mpr (show -q*a ≤ 0 by nlinarith)
    linarith
  rw [← ENNReal.ofReal_sub _ hn]
  congr 1
  ring

variable {β : Type*} [fβ : Fintype β] [mβ : MeasurableSpace β]
  [sβ : MeasurableSingletonClass β]

/-- Actual marked exponential holding law, including the cost of every
competing channel through its total rate. -/
theorem jumpClock_window_lower (rate : β → ℝ) (hr : ∀ b, 0 ≤ rate b)
    (ht : 0 < ∑ b, rate b) (b : β) (Q a d e : ℝ)
    (hQ : (∑ c, rate c) ≤ Q) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hb : e ≤ rate b) :
    ENNReal.ofReal (e*d*Real.exp (-Q*(a+d))) ≤
      jumpClockMeasure rate hr ht ({b} ×ˢ Ioc a (a+d)) := by
  letI := isProbabilityMeasure_expMeasure ht
  rw [jumpClockMeasure, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ b (measurableSet_singleton b),
    exponential_Ioc _ a d ht ha hd]
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (rate b/(∑ c,rate c))*ENNReal.ofReal _
  rw [← ENNReal.ofReal_mul (div_nonneg (hr b) ht.le)]
  exact ENNReal.ofReal_le_ofReal (holding_window_scalar_lower _ _ Q a d e ht hQ ha hd he hb)

end
end RandomViability
