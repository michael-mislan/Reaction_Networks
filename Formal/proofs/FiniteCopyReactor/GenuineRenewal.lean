import proofs.FiniteCopyReactor.BoundedClock
import proofs.FiniteCopyReactor.DummyResolvent
import proofs.FiniteCopyReactor.ScalarRenewal
import proofs.FiniteCopyReactor.SurvivalBounds

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal BigOperators

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] [Fintype β]

/-- At each positive-rate state, the bounded clock solves the genuine-event renewal.
No positive-rate assumption is imposed on other (possibly absorbing) states. -/
theorem bounded_clock_genuine_renewal (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (q : ℝ) (hq : 0 < q) (hb : ∀ x,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ y,f y ≤ 1) (x : α) (hx : 0 < ∑ b,rate x b) (T : ℝ) :
    let P := boundedClockKernel next rate hr q hq hb
    let C := causalClockEndpoint P q f
    C x T=f x*survivalKernel (∑ b,rate x b) T+
      positiveConvolution (survivalKernel (∑ b,rate x b))
        (fun u => ∑ b,ENNReal.ofReal (rate x b)*C (next x b) u) T := by
  let P := boundedClockKernel next rate hr q hq hb
  let C := causalClockEndpoint P q f
  let r := ∑ b,rate x b
  let H := fun u => ∑ b,ENNReal.ofReal (rate x b)*C (next x b) u
  let G := fun u => f x*survivalKernel r u+positiveConvolution (survivalKernel r) H u
  have hmC (y : α) : Measurable (C y) := by
    have hh := (causal_clock_measurable P q f).comp
      (show Measurable (fun u : ℝ => (u,y)) from measurable_id.prodMk measurable_const)
    exact hh
  have hmH : Measurable H := by
    apply Finset.measurable_sum
    intro b _
    exact measurable_const.mul (hmC _)
  have hC1 (y : α) (u : ℝ) : C y u ≤ 1 := causal_clock_le_one P q hq.le f hf y u
  have hCn (y : α) (u : ℝ) (hu : u < 0) : C y u=0 := if_neg (not_le.mpr hu)
  have hH1 (u : ℝ) : H u ≤ ENNReal.ofReal r := by
    calc
      _ ≤ ∑ b,ENNReal.ofReal (rate x b) := by
        apply Finset.sum_le_sum
        intro b _
        simpa only [mul_one] using mul_le_mul_right (hC1 (next x b) u) (ENNReal.ofReal (rate x b))
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun b _ => hr x b)).symm
  have hHn (u : ℝ) (hu : u < 0) : H u=0 := by
    simp only [H,hCn _ u hu,mul_zero,Finset.sum_const_zero]
  have hmG : Measurable G :=
    (measurable_const.mul (survival_kernel_measurable r)).add
      (positive_convolution_measurable _ H (survival_kernel_measurable r) hmH)
  have hG1 (u : ℝ) : G u ≤ 1 := survival_candidate_le_one r u hx (f x) (hf x) H hH1 hHn
  have hGn (u : ℝ) (hu : u < 0) : G u=0 := by
    dsimp [G]
    rw [survival_convolution_negative r u H hHn hu]
    simp only [survivalKernel,if_neg (not_le.mpr hu),mul_zero,add_zero]
  have heq : C x=G := scalar_dummy_renewal_unique q (q-r) hq (sub_nonneg.mpr (hb x))
    (by dsimp [r]; linarith) (C x) G
    (fun u => f x*survivalKernel q u+positiveConvolution (survivalKernel q) H u)
    (hmC x) hmG (causal_bounded_exponential_weight q hq.le (C x) (hC1 x) (hCn x))
    (causal_bounded_exponential_weight q hq.le G hG1 hGn)
    (fun u => bounded_clock_dummy_renewal next rate hr q hq hb f x u)
    (fun u => dummy_renewal_candidate q r u (hb x) (f x) H hmH)
  exact congrFun heq T

end
end FiniteCopyReactor
