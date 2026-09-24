import proofs.FiniteCopyReactor.CausalClock

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal BigOperators

variable {α β : Type*} [Fintype β]

/-- A common clock on any state space, with a literal self event for unused clock intensity. -/
def boundedClockKernel (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (q : ℝ) (hq : 0 < q) (hb : ∀ x,(∑ b,rate x b) ≤ q) :
    MarkedKernel α (Option β) where
  prob x j := match j with | none => 1-(∑ b,rate x b)/q | some b => rate x b/q
  next x j := match j with | none => x | some b => next x b
  mark _ := 0
  nonneg x j := by
    cases j with
    | none => exact sub_nonneg.mpr ((div_le_one hq).mpr (hb x))
    | some b => exact div_nonneg (hr x b) hq.le
  row_sum x := by
    rw [Fintype.sum_option]
    dsimp only
    rw [← Finset.sum_div]
    ring

theorem bounded_clock_weighted_row (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (q : ℝ) (hq : 0 < q) (hb : ∀ x,(∑ b,rate x b) ≤ q)
    (F : α → ℝ≥0∞) (x : α) :
    ENNReal.ofReal q*(∑ j,ENNReal.ofReal ((boundedClockKernel next rate hr q hq hb).prob x j)*
      F ((boundedClockKernel next rate hr q hq hb).next x j))=
      ENNReal.ofReal (q-(∑ b,rate x b))*F x+∑ b,ENNReal.ofReal (rate x b)*F (next x b) := by
  have hd : ENNReal.ofReal q*ENNReal.ofReal (1-(∑ b,rate x b)/q)=ENNReal.ofReal (q-(∑ b,rate x b)) := by
    rw [← ENNReal.ofReal_mul hq.le]
    congr 1
    field_simp
  have hj (b : β) : ENNReal.ofReal q*ENNReal.ofReal (rate x b/q)=ENNReal.ofReal (rate x b) := by
    rw [← ENNReal.ofReal_mul hq.le]
    congr 1
    field_simp
  rw [Fintype.sum_option]
  simp only [boundedClockKernel,mul_add,Finset.mul_sum,← mul_assoc,hd,hj]

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

theorem bounded_clock_dummy_renewal (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (q : ℝ) (hq : 0 < q) (hb : ∀ x,(∑ b,rate x b) ≤ q)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) :
    let P := boundedClockKernel next rate hr q hq hb
    let C := causalClockEndpoint P q f
    C x T=f x*survivalKernel q T+
      positiveConvolution (survivalKernel q) (fun u => ∑ b,ENNReal.ofReal (rate x b)*C (next x b) u) T+
      ENNReal.ofReal (q-(∑ b,rate x b))*positiveConvolution (survivalKernel q) (C x) T := by
  let P := boundedClockKernel next rate hr q hq hb
  let C := causalClockEndpoint P q f
  let H := fun u => ∑ b,ENNReal.ofReal (rate x b)*C (next x b) u
  let J := fun u => ∑ j,ENNReal.ofReal (P.prob x j)*C (P.next x j) u
  have hmC (y : α) : Measurable (C y) := by
    have hh := (causal_clock_measurable P q f).comp
      (show Measurable (fun u : ℝ => (u,y)) from measurable_id.prodMk measurable_const)
    exact hh
  have hmJ : Measurable J := by
    apply Finset.measurable_sum
    intro j _
    exact measurable_const.mul (hmC _)
  have hrow : (fun u => ENNReal.ofReal q*J u)=
      (fun u => ENNReal.ofReal (q-(∑ b,rate x b))*C x u+H u) := by
    funext u
    exact bounded_clock_weighted_row next rate hr q hq hb (fun y => C y u) x
  change C x T=f x*survivalKernel q T+positiveConvolution (survivalKernel q) H T+
    ENNReal.ofReal (q-(∑ b,rate x b))*positiveConvolution (survivalKernel q) (C x) T
  have he := causal_clock_survival_renewal P q hq.le f x T
  change C x T=f x*survivalKernel q T+ENNReal.ofReal q*positiveConvolution (survivalKernel q) J T at he
  rw [← positive_convolution_const_mul _ J (survival_kernel_measurable q) hmJ,hrow,
    positive_convolution_add_right _ _ _ (survival_kernel_measurable q) (measurable_const.mul (hmC x)),
    positive_convolution_const_mul _ _ (survival_kernel_measurable q) (hmC x)] at he
  exact he.trans (by ac_rfl)

end
end FiniteCopyReactor
