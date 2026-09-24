import proofs.FiniteCopyReactor.CountKilledProducts
import proofs.RandomViability.PredictableProductBounds
import proofs.FiniteReservoir.PhysicalLaplace
import proofs.RandomViability.JumpStateLaplace
import proofs.RandomViability.FoodCrossingAlgebra

namespace FiniteReservoir
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal
noncomputable section
variable {M : ℕ}
open FiniteCopyReactor (unit_jumpMultiplier_eq)
open FiniteCopyReactor (reactorFood reactorTrajectoryFood)
set_option maxHeartbeats 30000

def massRegion (B : ℕ) (N : CountState M) : Prop := reactorMass N ≤ B

def massKilledMultiplier (B k : ℕ)
    (h : Finset.Iic k → JumpState (CountState M) CompetitionChannel)
    (y : JumpState (CountState M) CompetitionChannel) : ℝ≥0∞ :=
  if massRegion B (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 then jumpMultiplier (fun _ => 1) 1 y else 0

theorem massKilledProduct_eq (B K : ℕ)
    (z : ℕ → JumpState (CountState M) CompetitionChannel)
    (hs : ∀ i < K, massRegion B (z i).1) :
    trajectoryProduct (massKilledMultiplier B) K z =
      ENNReal.ofReal (Real.exp (-waitingSum (fun i => (z (i+1)).2.2) K)) := by
  have he : trajectoryProduct (massKilledMultiplier B) K z =
      ∏ i : Fin K, ENNReal.ofReal (Real.exp (-(z ((i : ℕ)+1)).2.2)) := by
    unfold trajectoryProduct
    apply Finset.prod_congr rfl
    intro i _
    have hi : massRegion B ((Preorder.frestrictLe (i : ℕ) z)
      ⟨(i : ℕ), Finset.mem_Iic.mpr le_rfl⟩).1 := hs i i.isLt
    dsimp only [massKilledMultiplier]
    rw [if_pos hi, unit_jumpMultiplier_eq]
  rw [he, Fin.prod_univ_eq_prod_range (fun i => ENNReal.ofReal (Real.exp (-(z (i+1)).2.2))) K]
  have hf := food_product_formula (fun _ => 0) (fun i => (z (i+1)).2.2) 1 K
  simpa only [incomingSum, Finset.sum_const_zero, pow_zero, one_mul, neg_one_mul] using hf

theorem massKilledProduct_lower (B K : ℕ) (T : ℝ)
    (z : ℕ → JumpState (CountState M) CompetitionChannel)
    (hs : ∀ i < K, massRegion B (z i).1) (ht : waitingSum (fun i => (z (i+1)).2.2) K ≤ T) :
    ENNReal.ofReal (Real.exp (-T)) ≤ trajectoryProduct (massKilledMultiplier B) K z := by
  rw [massKilledProduct_eq B K z hs]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg ht))

theorem massKilledMultiplier_measurable (B k : ℕ) :
    Measurable (fun p : (Finset.Iic k → JumpState (CountState M) CompetitionChannel) ×
      JumpState (CountState M) CompetitionChannel => massKilledMultiplier (M := M) B k p.1 p.2) := by
  have hs : MeasurableSet {N : CountState M | massRegion B N} :=
    measurableSet_le (measurable_of_countable reactorMass) measurable_const
  exact Measurable.ite (hs.preimage (((measurable_pi_apply
    (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).comp measurable_fst).fst))
    ((jumpMultiplier_measurable _ _).comp measurable_snd) measurable_const

theorem physical_killed_product_bound (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) (B : ℕ) :
    ∃ q : ℝ, 1 ≤ q ∧ ∀ K,
      (∫⁻ z, trajectoryProduct (massKilledMultiplier B) K z ∂reactorTrajectory M p V hV N) ≤
        (ENNReal.ofReal (q/(q+1)))^K := by
  obtain ⟨q, hq, hb⟩ := reactor_locally_bounded M p V hV B
  refine ⟨q, hq, ?_⟩
  intro K
  apply predictable_product_integral_le (reactorTrajectory M p V hV N)
    (jumpHistoryKernel reactorNext (reactorRate M p V)
      (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV))
    (fun k => reactorTrajectory_transition M p V hV N k)
    (massKilledMultiplier B) (massKilledMultiplier_measurable B)
  intro k h
  by_cases hs : massRegion B (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1
  · simp only [massKilledMultiplier, if_pos hs]
    exact (jumpState_wait_contraction reactorNext (reactorRate M p V)
      (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)
      (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩).1 q (hb _ hs)).1
  · simp only [massKilledMultiplier, if_neg hs, lintegral_zero]
    exact bot_le

end
end FiniteReservoir
