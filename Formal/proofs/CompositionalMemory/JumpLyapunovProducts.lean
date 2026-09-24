import proofs.CompositionalMemory.JumpLyapunov
import proofs.RandomViability.JumpSupport
import proofs.RandomViability.PredictableProductCrossing

namespace CompositionalMemory
open RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def lyapunovMultiplier {α β : Type*} (V : α → ℝ) (c : ℝ) (k : ℕ)
    (h : Finset.Iic k → JumpState α β) (y : JumpState α β) : ℝ≥0∞ :=
  ENNReal.ofReal (V y.1/V (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1)*
    ENNReal.ofReal (Real.exp (-c*y.2.2))

theorem lyapunovMultiplier_measurable {α β : Type*}
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (V : α → ℝ) (c : ℝ) (k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState α β) × JumpState α β =>
      lyapunovMultiplier V c k p.1 p.2) := by
  unfold lyapunovMultiplier
  have hv := measurable_of_countable V
  exact (((hv.comp measurable_snd.fst).div
    (hv.comp (((measurable_pi_apply _).comp measurable_fst).fst))).ennreal_ofReal).mul
      (by fun_prop)

theorem lyapunovMultiplier_mean {α β : Type*}
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b)
    (V : α → ℝ) (hV : ∀ x, 0 < V x) (c : ℝ) (hc : 0 ≤ c)
    (hgen : ∀ x, (∑ b, rate x b*(V (next x b)-V x)) ≤ c*V x)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) :
    (∫⁻ y, lyapunovMultiplier V c k h y ∂jumpHistoryKernel next rate hr ht k h) ≤ 1 := by
  let x := (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1
  change (∫⁻ y, lyapunovMultiplier V c k h y ∂jumpStateKernel next rate hr ht x) ≤ 1
  have he : ∀ᵐ y ∂jumpStateKernel next rate hr ht x,
      lyapunovMultiplier V c k h y = jumpMultiplier (fun b => V (next x b)/V x) c y := by
    filter_upwards [jumpStateKernel_consistent next rate hr ht x] with y hy
    obtain ⟨b,hb,hs⟩ := hy
    simp only [lyapunovMultiplier,jumpMultiplier,hb,Sum.elim_inr,hs,x]
  rw [lintegral_congr_ae he]
  exact jump_lyapunov_step next rate hr ht V hV c hc hgen x

/-- The product telescopes for every marked path; no path independence is used. -/
theorem lyapunov_product_formula {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (V : α → ℝ) (hV : ∀ x, 0 < V x) (c : ℝ)
    (z : ℕ → JumpState α β) (K : ℕ) :
    trajectoryProduct (lyapunovMultiplier V c) K z =
      ENNReal.ofReal (V (z K).1/V (z 0).1 *
        Real.exp (-c*(∑ i ∈ Finset.range K, (z (i+1)).2.2))) := by
  induction K with
  | zero => simp [trajectoryProduct,div_self (ne_of_gt (hV _))]
  | succ K ih =>
    rw [trajectoryProduct_succ,ih]
    change ENNReal.ofReal (V (z K).1/V (z 0).1*Real.exp (-c*(∑ i ∈ Finset.range K,(z (i+1)).2.2))) *
      (ENNReal.ofReal (V (z (K+1)).1/V (z K).1)*ENNReal.ofReal (Real.exp (-c*(z (K+1)).2.2))) = _
    rw [← ENNReal.ofReal_mul (div_pos (hV _) (hV _)).le,
      ← ENNReal.ofReal_mul (mul_pos (div_pos (hV _) (hV _)) (Real.exp_pos _)).le,
      Finset.sum_range_succ]
    congr 1
    rw [mul_add,Real.exp_add]
    field_simp [ne_of_gt (hV (z K).1),ne_of_gt (hV (z 0).1)]

end CompositionalMemory
