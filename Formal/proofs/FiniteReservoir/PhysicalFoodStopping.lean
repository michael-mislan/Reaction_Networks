import proofs.RandomViability.FoodCrossingAlgebra
import proofs.FiniteReservoir.PhysicalStoppedProducts
import proofs.FiniteReservoir.PhysicalLaplace

namespace FiniteReservoir
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal
noncomputable section
variable {M : ℕ}
open FiniteCopyReactor (reactorFood reactorTrajectoryFood)
set_option maxHeartbeats 30000

def foodHistorySum (k : ℕ)
    (h : Finset.Iic k → JumpState (CountState M) CompetitionChannel) : ℕ :=
  ∑ i : Fin k, reactorTrajectoryFood (h ⟨(i : ℕ)+1, Finset.mem_Iic.mpr i.isLt⟩).2.1

def foodBudgetStop (b k : ℕ)
    (h : Finset.Iic k → JumpState (CountState M) CompetitionChannel) : Prop :=
  b ≤ foodHistorySum (M := M) k h

theorem foodHistorySum_restrict (k : ℕ)
    (z : ℕ → JumpState (CountState M) CompetitionChannel) :
    foodHistorySum (M := M) k (Preorder.frestrictLe k z) = incomingSum (fun i => reactorTrajectoryFood (z (i+1)).2.1) k := by
  exact Fin.sum_univ_eq_sum_range (fun i => reactorTrajectoryFood (z (i+1)).2.1) k

theorem food_multiplier_eq (s : ℝ)
    (y : JumpState (CountState M) CompetitionChannel) :
    jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) s y =
      ENNReal.ofReal ((2 : ℝ)^reactorTrajectoryFood y.2.1 * Real.exp (-s*y.2.2)) := by
  have hw : y.2.1.elim (fun _ => (1 : ℝ)) (fun ch => (2 : ℝ)^reactorFood ch) =
      (2 : ℝ)^reactorTrajectoryFood y.2.1 := by
    cases y.2.1 <;> rfl
  unfold jumpMultiplier
  rw [hw, ← ENNReal.ofReal_mul (by positivity)]

theorem physical_stopped_product_eq (s : ℝ) (b K : ℕ)
    (z : ℕ → JumpState (CountState M) CompetitionChannel) :
    trajectoryProduct (fun k h y => if foodBudgetStop b k h then 1 else
      jumpMultiplier (fun ch => (2 : ℝ)^reactorFood ch) s y) K z =
    foodStoppedProduct (fun i => reactorTrajectoryFood (z (i+1)).2.1) (fun i => (z (i+1)).2.2) s b K := by
  unfold trajectoryProduct foodStoppedProduct
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  have he : foodBudgetStop b i (Preorder.frestrictLe (i : ℕ) z) ↔
      b ≤ incomingSum (fun l => reactorTrajectoryFood (z (l+1)).2.1) i := by
    unfold foodBudgetStop
    rw [foodHistorySum_restrict]
  by_cases hs : foodBudgetStop b i (Preorder.frestrictLe (i : ℕ) z)
  · rw [if_pos hs, if_pos (he.mp hs)]
  · rw [if_neg hs, if_neg (fun h => hs (he.mpr h)), food_multiplier_eq]

theorem reactorTrajectoryFood_measurable : Measurable reactorTrajectoryFood :=
  measurable_const.sumElim (measurable_of_countable reactorFood)

theorem foodHistorySum_measurable (k : ℕ) : Measurable (foodHistorySum (M := M) k) := by
  unfold foodHistorySum
  apply Finset.measurable_sum
  intro i _
  exact reactorTrajectoryFood_measurable.comp
    (measurable_pi_apply (⟨(i : ℕ)+1, Finset.mem_Iic.mpr i.isLt⟩ : Finset.Iic k)).snd.fst

theorem foodHistorySum_stop_measurable (b k : ℕ) : MeasurableSet {h | b ≤ foodHistorySum (M := M) k h} :=
  measurableSet_le measurable_const (foodHistorySum_measurable k)

end
end FiniteReservoir
