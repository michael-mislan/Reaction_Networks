import proofs.FiniteCopyReactor.EndpointClockIntegral
import proofs.RandomViability.WeightedRenewal

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

variable {α β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem exponential_two_rate_weight (r q T : ℝ) (hr : 0 < r) (hq : 0 ≤ q) :
    (∫⁻ w,ENNReal.ofReal (Real.exp (q*(T-w))) ∂expMeasure r)=
      ENNReal.ofReal (Real.exp (q*T))*ENNReal.ofReal (r/(r+q)) := by
  have he (w : ℝ) : Real.exp (q*(T-w))=Real.exp (q*T)*Real.exp (-q*w) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he,ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop),exponential_laplace_lintegral r q hr (by linarith)]

theorem jump_clock_half_weight (rate : β → ℝ) (hr : ∀ b,0 ≤ rate b) (ht : 0 < ∑ b,rate b)
    (q T : ℝ) (hbound : (∑ b,rate b) ≤ q) :
    (∫⁻ y : β × ℝ,ENNReal.ofReal (Real.exp (q*(T-y.2))) ∂jumpClockMeasure rate hr ht) ≤
      ENNReal.ofReal (1/2:ℝ)*ENNReal.ofReal (Real.exp (q*T)) := by
  have hq : 0 ≤ q := ht.le.trans hbound
  rw [jump_clock_integral rate hr ht _ (by fun_prop)]
  simp_rw [exponential_two_rate_weight _ q T ht hq]
  rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg (fun b _ => div_nonneg (hr b) ht.le),
    ← Finset.sum_div,div_self (ne_of_gt ht),ENNReal.ofReal_one,one_mul]
  rw [mul_comm]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (show 0 < (∑ b,rate b)+q by linarith)).mpr
  linarith

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

omit [Countable α] [MeasurableSingletonClass α] in
/-- Bounded causal endpoint solutions of the same physical first-jump equation agree. -/
theorem bounded_endpoint_renewal_unique (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (q : ℝ) (hbound : ∀ x,(∑ b,rate x b) ≤ q)
    (F G B : ℝ × α → ℝ≥0∞) (hFm : Measurable F) (hGm : Measurable G)
    (hF1 : ∀ p,F p ≤ 1) (hG1 : ∀ p,G p ≤ 1)
    (hFn : ∀ p,p.1 < 0 → F p=0) (hGn : ∀ p,p.1 < 0 → G p=0)
    (hF : ∀ p,F p=B p+∫⁻ y,F (p.1-y.2,next p.2 y.1) ∂jumpClockMeasure (rate p.2) (hr p.2) (ht p.2))
    (hG : ∀ p,G p=B p+∫⁻ y,G (p.1-y.2,next p.2 y.1) ∂jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)) : F=G := by
  let step := fun (p : ℝ × α) (y : β × ℝ) => (p.1-y.2,next p.2 y.1)
  have hm (p : ℝ × α) : Measurable (step p) :=
    (measurable_const.sub measurable_snd).prodMk ((measurable_of_countable (next p.2)).comp measurable_fst)
  let μ := fun p : ℝ × α => (jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)).map (step p)
  let w := fun p : ℝ × α => Real.exp (q*p.1)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hweight (p : ℝ × α) : (∫⁻ a,ENNReal.ofReal (w a) ∂μ p) ≤
      ENNReal.ofReal (1/2:ℝ)*ENNReal.ofReal (w p) := by
    change (∫⁻ a,ENNReal.ofReal (w a) ∂(jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)).map (step p)) ≤ _
    rw [lintegral_map hw.ennreal_ofReal (hm p)]
    exact jump_clock_half_weight (rate p.2) (hr p.2) (ht p.2) q p.1 (hbound p.2)
  have hfw (H : ℝ × α → ℝ≥0∞) (h1 : ∀ p,H p ≤ 1) (hn : ∀ p,p.1 < 0 → H p=0) (p : ℝ × α) :
      H p ≤ ENNReal.ofReal (w p) := by
    by_cases hp : 0 ≤ p.1
    · have hq : 0 ≤ q := (ht p.2).le.trans (hbound p.2)
      exact (h1 p).trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hq hp)))
    · rw [hn p (lt_of_not_ge hp)]
      exact bot_le
  apply weighted_half_renewal_unique μ F G B w hFm hGm hw (hfw F hF1 hFn) (hfw G hG1 hGn)
  · intro p
    change F p=B p+∫⁻ a,F a ∂(jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)).map (step p)
    rw [lintegral_map hFm (hm p)]
    exact hF p
  · intro p
    change G p=B p+∫⁻ a,G a ∂(jumpClockMeasure (rate p.2) (hr p.2) (ht p.2)).map (step p)
    rw [lintegral_map hGm (hm p)]
    exact hG p
  · exact hweight

end
end FiniteCopyReactor
