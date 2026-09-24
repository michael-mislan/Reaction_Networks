import proofs.RandomViability.FoodCrossingAlgebra
import proofs.RandomViability.StoppedPhysicalProducts
import proofs.RandomViability.PhysicalMassTrajectory

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

def foodHistorySum {n : ℕ} (k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : ℕ :=
  ∑ i : Fin k, trajectoryFoodInput (h ⟨(i : ℕ)+1, Finset.mem_Iic.mpr i.isLt⟩).2.1

def foodBudgetStop {n : ℕ} (b k : ℕ)
    (h : Finset.Iic k → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  b ≤ foodHistorySum k h

theorem foodHistorySum_restrict {n : ℕ} (k : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    foodHistorySum k (Preorder.frestrictLe k z) = incomingSum (fun i => trajectoryFoodInput (z (i+1)).2.1) k := by
  exact Fin.sum_univ_eq_sum_range (fun i => trajectoryFoodInput (z (i+1)).2.1) k

theorem food_multiplier_eq {n : ℕ} (s : ℝ)
    (y : JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    jumpMultiplier (fun ch => (2 : ℝ)^foodInputMass ch) s y =
      ENNReal.ofReal ((2 : ℝ)^trajectoryFoodInput y.2.1 * Real.exp (-s*y.2.2)) := by
  have hw : y.2.1.elim (fun _ => (1 : ℝ)) (fun ch => (2 : ℝ)^foodInputMass ch) =
      (2 : ℝ)^trajectoryFoodInput y.2.1 := by
    cases y.2.1 <;> rfl
  unfold jumpMultiplier
  rw [hw, ← ENNReal.ofReal_mul (by positivity)]

theorem physical_stopped_product_eq {n : ℕ} (s : ℝ) (b K : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :
    trajectoryProduct (fun k h y => if foodBudgetStop b k h then 1 else
      jumpMultiplier (fun ch => (2 : ℝ)^foodInputMass ch) s y) K z =
    foodStoppedProduct (fun i => trajectoryFoodInput (z (i+1)).2.1) (fun i => (z (i+1)).2.2) s b K := by
  unfold trajectoryProduct foodStoppedProduct
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  have he : foodBudgetStop b i (Preorder.frestrictLe (i : ℕ) z) ↔
      b ≤ incomingSum (fun l => trajectoryFoodInput (z (l+1)).2.1) i := by
    unfold foodBudgetStop
    rw [foodHistorySum_restrict]
  by_cases hs : foodBudgetStop b i (Preorder.frestrictLe (i : ℕ) z)
  · rw [if_pos hs, if_pos (he.mp hs)]
  · rw [if_neg hs, if_neg (fun h => hs (he.mpr h)), food_multiplier_eq]

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem trajectoryFoodInput_measurable : Measurable (@trajectoryFoodInput n) :=
  measurable_const.sumElim (measurable_of_countable foodInputMass)

theorem foodHistorySum_measurable (k : ℕ) : Measurable (@foodHistorySum n k) := by
  unfold foodHistorySum
  apply Finset.measurable_sum
  intro i _
  exact trajectoryFoodInput_measurable.comp
    (measurable_pi_apply (⟨(i : ℕ)+1, Finset.mem_Iic.mpr i.isLt⟩ : Finset.Iic k)).snd.fst

theorem foodHistorySum_stop_measurable (b k : ℕ) : MeasurableSet {h | b ≤ @foodHistorySum n k h} :=
  measurableSet_le measurable_const (foodHistorySum_measurable k)

end
end RandomViability
