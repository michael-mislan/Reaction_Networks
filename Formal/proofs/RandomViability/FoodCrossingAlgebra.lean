import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace RandomViability
open Classical
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 30000

def incomingSum (f : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, f i
def waitingSum (t : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, t i
def foodStoppedProduct (f : ℕ → ℕ) (t : ℕ → ℝ) (s : ℝ) (b K : ℕ) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range K, if b ≤ incomingSum f i then 1 else
    ENNReal.ofReal ((2 : ℝ)^f i * Real.exp (-s*t i))

theorem incomingSum_mono (f : ℕ → ℕ) : Monotone (incomingSum f) := by
  intro j k hjk
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hjk)

theorem food_product_formula (f : ℕ → ℕ) (t : ℕ → ℝ) (s : ℝ) (K : ℕ) :
    (∏ i ∈ Finset.range K, ENNReal.ofReal ((2 : ℝ)^f i * Real.exp (-s*t i))) =
      ENNReal.ofReal ((2 : ℝ)^incomingSum f K * Real.exp (-s*waitingSum t K)) := by
  unfold incomingSum waitingSum
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [pow_add, show -s*((∑ i ∈ Finset.range K, t i)+t K) =
      -s*(∑ i ∈ Finset.range K, t i)+(-s*t K) by ring, Real.exp_add]
    ring

theorem food_stopped_at_crossing (f : ℕ → ℕ) (t : ℕ → ℝ) (s : ℝ) (b j K : ℕ)
    (hjK : j ≤ K) (hbefore : ∀ i < j, incomingSum f i < b) (hcross : b ≤ incomingSum f j) :
    foodStoppedProduct f t s b K =
      ENNReal.ofReal ((2 : ℝ)^incomingSum f j * Real.exp (-s*waitingSum t j)) := by
  have he : foodStoppedProduct f t s b j = foodStoppedProduct f t s b K := by
    apply Finset.prod_subset (Finset.range_mono hjK)
    intro i _ hi
    have hji : j ≤ i := by simpa using hi
    exact if_pos (hcross.trans (incomingSum_mono f hji))
  rw [← he]
  unfold foodStoppedProduct
  have hu : (∏ i ∈ Finset.range j, if b ≤ incomingSum f i then 1 else
      ENNReal.ofReal ((2 : ℝ)^f i * Real.exp (-s*t i))) =
      ∏ i ∈ Finset.range j, ENNReal.ofReal ((2 : ℝ)^f i * Real.exp (-s*t i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact if_neg (not_le_of_gt (hbefore i (Finset.mem_range.mp hi)))
  rw [hu, food_product_formula]

theorem food_crossing_multiplier_lower (f : ℕ → ℕ) (t : ℕ → ℝ) (s T : ℝ) (hs : 0 ≤ s)
    (b j K : ℕ) (hjK : j ≤ K) (hbefore : ∀ i < j, incomingSum f i < b)
    (hcross : b ≤ incomingSum f j) (htime : waitingSum t j ≤ T) :
    ENNReal.ofReal ((2 : ℝ)^b * Real.exp (-s*T)) ≤ foodStoppedProduct f t s b K := by
  rw [food_stopped_at_crossing f t s b j K hjK hbefore hcross]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcross)
    (Real.exp_le_exp.mpr (by nlinarith)) (by positivity) (by positivity)

end
end RandomViability
