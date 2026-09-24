import proofs.FiniteCopyReactor.GenuineRenewal
import proofs.FiniteCopyReactor.JumpConvolution

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal BigOperators

variable {α β : Type*} [Fintype β]

def stoppedRate (D : Set α) (rate : α → β → ℝ) (x : α) (b : β) : ℝ := if x ∈ D then rate x b else 0

omit [Fintype β] in
theorem stopped_rate_nonneg (D : Set α) (rate : α → β → ℝ) (hr : ∀ x b,0 ≤ rate x b) :
    ∀ x b,0 ≤ stoppedRate D rate x b := by
  intro x b
  unfold stoppedRate
  split_ifs
  · exact hr x b
  · exact le_rfl

theorem stopped_rate_bound (D : Set α) (rate : α → β → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q) : ∀ x,(∑ b,stoppedRate D rate x b) ≤ q := by
  intro x
  by_cases hx : x ∈ D
  · simpa only [stoppedRate,if_pos hx] using hb x hx
  · simpa only [stoppedRate,if_neg hx,Finset.sum_const_zero] using hq

def stoppedClockKernel (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (q : ℝ) (hq : 0 < q) (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q) :
    MarkedKernel α (Option β) :=
  boundedClockKernel next (stoppedRate D rate) (stopped_rate_nonneg D rate hr) q hq
    (stopped_rate_bound D rate q hq.le hb)

theorem stopped_clock_outside (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (q : ℝ) (hq : 0 < q) (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (x : α) (hx : x ∉ D) (hf : f x=0) (T : ℝ) :
    causalClockEndpoint (stoppedClockKernel D next rate hr q hq hb) q f x T=0 := by
  have he (n : ℕ) : tickValue (stoppedClockKernel D next rate hr q hq hb) n f x=0 := by
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [tickValue,Fintype.sum_option]
      simp only [stoppedClockKernel,boundedClockKernel,stoppedRate,if_neg hx,Finset.sum_const_zero,
        zero_div,sub_zero,ENNReal.ofReal_one,ENNReal.ofReal_zero,zero_mul,one_mul,add_zero]
      exact ih
  unfold causalClockEndpoint
  split_ifs
  · simp only [clockEndpoint,he,mul_zero,tsum_zero]
  · rfl

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

theorem stopped_clock_active_renewal (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (q : ℝ) (hq : 0 < q) (hb : ∀ x ∈ D,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ y,f y ≤ 1) (x : α) (hx : x ∈ D) (ht : 0 < ∑ b,rate x b) (T : ℝ) :
    let C := causalClockEndpoint (stoppedClockKernel D next rate hr q hq hb) q f
    C x T=f x*survivalKernel (∑ b,rate x b) T+
      ∫⁻ y,C (next x y.1) (T-y.2) ∂jumpClockMeasure (rate x) (hr x) ht := by
  let P := stoppedClockKernel D next rate hr q hq hb
  let C := causalClockEndpoint P q f
  have hxrate : stoppedRate D rate x=rate x := by funext b; exact if_pos hx
  have hpos : 0 < ∑ b,stoppedRate D rate x b := by rw [hxrate]; exact ht
  have he := bounded_clock_genuine_renewal next (stoppedRate D rate) (stopped_rate_nonneg D rate hr)
    q hq (stopped_rate_bound D rate q hq.le hb) f hf x hpos T
  change C x T=f x*survivalKernel (∑ b,stoppedRate D rate x b) T+
    positiveConvolution (survivalKernel (∑ b,stoppedRate D rate x b))
      (fun u => ∑ b,ENNReal.ofReal (stoppedRate D rate x b)*C (next x b) u) T at he
  rw [hxrate] at he
  have hm (b : β) : Measurable (C (next x b)) := by
    have hh := (causal_clock_measurable P q f).comp
      (show Measurable (fun u : ℝ => (u,next x b)) from measurable_id.prodMk measurable_const)
    exact hh
  have hi := jump_continuation_convolution (rate x) (hr x) ht (fun b => C (next x b)) hm T
  exact he.trans (congrArg (fun z => f x*survivalKernel (∑ b,rate x b) T+z) hi.symm)

end
end FiniteCopyReactor
