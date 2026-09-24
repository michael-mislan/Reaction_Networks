import proofs.RandomViability.PredictableProducts
import proofs.FiniteCopyReactor.CountLaplace
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace FiniteCopyReactor
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

theorem stopped_physical_product_integral (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState Counts CompetitionChannel) → Prop)
    (hstop : ∀ k, MeasurableSet {h | stop k h}) (K : ℕ) :
    ∫⁻ z, trajectoryProduct
      (fun k h y => if stop k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) (2*V) y) K z
      ∂reactorTrajectory V r d hV hr hd N = 1 := by
  apply predictable_product_integral (reactorTrajectory V r d hV hr hd N)
    (jumpHistoryKernel reactorNext (reactorRate V r d)
      (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd))
    (fun k => reactorTrajectory_transition V r d hV hr hd N k)
  · intro k
    exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
      ((jumpMultiplier_measurable _ _).comp measurable_snd)
  · intro k h
    by_cases hs : stop k h
    · simp only [if_pos hs]
      simp
    · simp only [if_neg hs]
      exact reactor_food_multiplier_integral V r d hV hr hd
        (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1

theorem stopped_physical_product_tail (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState Counts CompetitionChannel) → Prop)
    (hstop : ∀ k, MeasurableSet {h | stop k h}) (K : ℕ) (ε : ℝ≥0∞) :
    ε * reactorTrajectory V r d hV hr hd N
      {z | ε ≤ trajectoryProduct (fun k h y => if stop k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) (2*V) y) K z} ≤ 1 := by
  let m := fun k h (y : JumpState Counts CompetitionChannel) => if stop k h then (1 : ℝ≥0∞) else
    jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) (2*V) y
  have hm : ∀ k, Measurable (fun p :
      (Finset.Iic k → JumpState Counts CompetitionChannel) ×
        JumpState Counts CompetitionChannel => m k p.1 p.2) := by
    intro k
    exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
      ((jumpMultiplier_measurable _ _).comp measurable_snd)
  have hp : Measurable (trajectoryProduct m K) :=
    (prefixProduct_measurable m hm K).comp (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ => JumpState Counts CompetitionChannel) K)
  have h := mul_meas_ge_le_lintegral (μ := reactorTrajectory V r d hV hr hd N) hp ε
  have he : (∫⁻ z, trajectoryProduct m K z ∂reactorTrajectory V r d hV hr hd N) = 1 :=
    stopped_physical_product_integral V r d hV hr hd N stop hstop K
  rw [he] at h
  exact h

end
end FiniteCopyReactor
