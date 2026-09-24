import proofs.InheritedCellAssay.FiniteSource

namespace InheritedCellAssay
open scoped BigOperators

theorem count_first_moment (F : ℕ) : countExpectation F (fun h => (h : ℚ)) = F/2 := by
  unfold countExpectation
  have hs : (∑ h ∈ Finset.range (F+1), (F.choose h : ℚ) * h) =
      (F : ℚ) * 2^(F-1) := by
    exact_mod_cast (by simpa [mul_comm] using Nat.sum_range_mul_choose F)
  rw [hs]
  cases F with
  | zero => norm_num
  | succ n =>
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

theorem source_affine (F : ℕ) (a b : ℚ) :
    sourceExpectation F (fun s => a*(s.card : ℚ)+b) = a*(F/2)+b := by
  have hm := source_count_transport F (fun h => (h : ℚ))
  rw [count_first_moment] at hm
  unfold sourceExpectation at *
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [add_div, mul_div_assoc, hm]
  congr 1
  simp [nsmul_eq_mul]

end InheritedCellAssay
