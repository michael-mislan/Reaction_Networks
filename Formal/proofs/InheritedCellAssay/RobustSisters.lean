import proofs.InheritedCellAssay.FiniteSource

namespace InheritedCellAssay
open scoped BigOperators

/-- Conditional H count among 2F daughters when k pairs are identical.
The other pairs each supply exactly one H and one L. -/
def daughterHigh (F k j : ℕ) : ℕ := F-k+2*j

def conditionalRisk (F k : ℕ) : ℚ :=
  countExpectation k (fun j =>
    if |selectiveFraction (2*F) (daughterHigh F k j)-8/9| > 1/10 then 1 else 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem conditional_thirty_bound (k : Fin 31) :
    conditionalRisk 30 k ≤ 2061197/67108864 := by
  fin_cases k <;>
    norm_num [conditionalRisk, countExpectation, daughterHigh, selectiveFraction,
      Finset.sum_range_succ, Nat.choose, abs_of_nonneg, abs_of_neg]

/-- Arbitrary dependence in which pairs are identical is permitted.
Only the fair independent signs conditional on k are retained. -/
def mixtureRisk (w : Fin 31 → ℚ) : ℚ := ∑ k, w k * conditionalRisk 30 k

theorem robust_thirty_bound (w : Fin 31 → ℚ)
    (hw : ∀ k, 0 ≤ w k) (hn : ∑ k, w k = 1) :
    mixtureRisk w ≤ 2061197/67108864 := by
  calc
    mixtureRisk w ≤ ∑ k, w k * (2061197/67108864) := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
        (conditional_thirty_bound k) (hw k))
    _ = 2061197/67108864 := by rw [← Finset.sum_mul, hn, one_mul]

theorem robust_thirty_design (w : Fin 31 → ℚ)
    (hw : ∀ k, 0 ≤ w k) (hn : ∑ k, w k = 1) : mixtureRisk w < 1/20 := by
  exact (robust_thirty_bound w hw hn).trans_lt (by norm_num)

end InheritedCellAssay
