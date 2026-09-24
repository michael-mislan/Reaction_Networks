import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PhosphorylationMemory

/-- Summing identical per-choice association propensities removes multiplicity. -/
theorem association_multiplicity (m : ℕ) (hm : m ≠ 0) (a e x : ℝ) :
    (∑ _i : Fin m, (a / (m : ℝ)) * e * x) = a * e * x := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp [hn]

/-- Vertex grouping after the multiplicity calculation, for arbitrary states. -/
theorem association_level {ι : Type*} [Fintype ι]
    (m : ℕ) (hm : m ≠ 0) (a e : ℝ) (x : ι → ℝ) :
    (∑ v, ∑ _i : Fin m, (a / (m : ℝ)) * e * x v) =
      a * e * ∑ v, x v := by
  simp_rw [association_multiplicity m hm]
  rw [Finset.mul_sum]

/-- Literal jump contribution for a scalar quadratic, with no Taylor remainder. -/
theorem quadratic_jump (x center jump volume p : ℝ) (hv : volume ≠ 0) :
    volume * (p * (x + jump / volume - center)^2 - p * (x-center)^2) =
      2 * (x-center) * p * jump + p * jump^2 / volume := by
  field_simp [hv]
  ring

end PhosphorylationMemory
