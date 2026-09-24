import proofs.RandomViability.PredictableProducts
import proofs.FiniteReservoir.PhysicalLaplace
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace FiniteReservoir
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal
noncomputable section
open FiniteCopyReactor (reactorFood)
set_option maxHeartbeats 30000

theorem stopped_physical_product_integral (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (CountState M) CompetitionChannel) → Prop)
    (hstop : ∀ k, MeasurableSet {h | stop k h}) (K : ℕ) :
    ∫⁻ z, trajectoryProduct
      (fun k h y => if stop k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) (2*V) y) K z
      ∂reactorTrajectory M p V hV N = 1 := by
  apply predictable_product_integral (reactorTrajectory M p V hV N)
    (jumpHistoryKernel reactorNext (reactorRate M p V)
      (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV))
    (fun k => reactorTrajectory_transition M p V hV N k)
  · intro k
    exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
      ((jumpMultiplier_measurable _ _).comp measurable_snd)
  · intro k h
    by_cases hs : stop k h
    · simp only [if_pos hs]
      simp
    · simp only [if_neg hs]
      exact reactor_food_multiplier_integral M p V hV
        (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1

theorem stopped_physical_product_tail (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState (CountState M) CompetitionChannel) → Prop)
    (hstop : ∀ k, MeasurableSet {h | stop k h}) (K : ℕ) (ε : ℝ≥0∞) :
    ε * reactorTrajectory M p V hV N
      {z | ε ≤ trajectoryProduct (fun k h y => if stop k h then 1 else
        jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) (2*V) y) K z} ≤ 1 := by
  let m := fun k h (y : JumpState (CountState M) CompetitionChannel) => if stop k h then (1 : ℝ≥0∞) else
    jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) (2*V) y
  have hm : ∀ k, Measurable (fun p :
      (Finset.Iic k → JumpState (CountState M) CompetitionChannel) ×
        JumpState (CountState M) CompetitionChannel => m k p.1 p.2) := by
    intro k
    exact Measurable.ite ((hstop k).preimage measurable_fst) measurable_const
      ((jumpMultiplier_measurable _ _).comp measurable_snd)
  have hp : Measurable (trajectoryProduct m K) :=
    (prefixProduct_measurable m hm K).comp (Preorder.measurable_frestrictLe
      (X := fun _ : ℕ => JumpState (CountState M) CompetitionChannel) K)
  have h := mul_meas_ge_le_lintegral (μ := reactorTrajectory M p V hV N) hp ε
  have he : (∫⁻ z, trajectoryProduct m K z ∂reactorTrajectory M p V hV N) = 1 :=
    stopped_physical_product_integral M p V hV N stop hstop K
  rw [he] at h
  exact h

end
end FiniteReservoir
