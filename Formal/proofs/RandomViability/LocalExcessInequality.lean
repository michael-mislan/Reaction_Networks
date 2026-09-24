import proofs.RandomViability.LocalOutputExclusion

set_option Elab.async false
namespace RandomViability
open Classical
noncomputable section
set_option maxHeartbeats 40000

/-- Excess-count control retains every correlation in the underlying finite law. -/
theorem finite_weighted_excess_bound {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x,0 ≤ w x) (L : Ω → ℕ) :
    (∑ x,if 2 ≤ L x then w x else 0) ≤
      (∑ x,w x*(L x : ℝ))-(∑ x,if 1 ≤ L x then w x else 0) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases h2 : 2 ≤ L x
  · rw [if_pos h2,if_pos (by omega : 1 ≤ L x)]
    have hc : (2 : ℝ) ≤ L x := by exact_mod_cast h2
    have hh := mul_le_mul_of_nonneg_left hc (hw x)
    linarith only [hh]
  · by_cases h1 : 1 ≤ L x
    · have he : L x = 1 := by omega
      simp [he]
    · have he : L x = 0 := by omega
      simp [he]

theorem one_sub_pow_le_mul (h : ℝ) (h1 : h ≤ 1) (Z : ℕ) :
    1-(1-h)^Z ≤ (Z : ℝ)*h := by
  induction Z with
  | zero => simp
  | succ Z ih =>
    have hp : 0 ≤ (1-h)^Z := pow_nonneg (by linarith) _
    have hh := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr h1)
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,mul_nonneg (show (0 : ℝ) ≤ Z by positivity) (sq_nonneg h)]

theorem finite_union_excess_le_square (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) (Z : ℕ) :
    (Z : ℝ)*h-(1-(1-h)^Z) ≤ (Z : ℝ)^2*h^2 := by
  induction Z with
  | zero => simp
  | succ Z ih =>
    have hh := mul_le_mul_of_nonneg_left (one_sub_pow_le_mul h h1 Z) h0
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    have hz : (0 : ℝ) ≤ Z := by positivity
    nlinarith only [ih,hh,mul_nonneg hz (sq_nonneg h),sq_nonneg h]

end
end RandomViability
