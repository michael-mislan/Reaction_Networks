import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace ACRZeroDivisors
open scoped BigOperators

theorem weighted_residual_bound {ι : Type*} [Fintype ι]
    (q f Q eps : ι → ℝ) (hq : ∀ i, |q i| ≤ Q i)
    (hf : ∀ i, |f i| ≤ eps i) :
    |∑ i, q i * f i| ≤ ∑ i, Q i * eps i := by
  calc
    _ ≤ ∑ i, |q i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul (hq i) (hf i) (abs_nonneg _) (le_trans (abs_nonneg _) (hq i))

theorem residual_bound (e h h0 B : ℝ) (hh : 0 < h0)
    (hf : h0 ≤ |h|) (hb : |e*h| ≤ B) : |e| ≤ B/h0 := by
  apply (le_div_iff₀ hh).2
  calc
    |e| * h0 ≤ |e| * |h| := mul_le_mul_of_nonneg_left hf (abs_nonneg _)
    _ = |e*h| := (abs_mul _ _).symm
    _ ≤ B := hb

theorem signed_loading_bound {ι : Type*} [Fintype ι]
    (e h h0 eta : ℝ) (q f d Q eps : ι → ℝ)
    (hid : e*h = ∑ i, q i*f i) (hh : 0 < h0) (hf : h0 ≤ |h|)
    (hq : ∀ i, |q i| ≤ Q i) (hr : ∀ i, |f i+d i| ≤ eps i)
    (hd : |∑ i, q i*d i| ≤ eta) :
    |e| ≤ ((∑ i, Q i*eps i)+eta)/h0 := by
  apply residual_bound e h h0 _ hh hf
  rw [hid]
  have heq : (∑ i, q i*f i) = (∑ i, q i*(f i+d i)) - ∑ i, q i*d i := by
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add (weighted_residual_bound q (fun i => f i+d i) Q eps hq hr) hd)

theorem coupling_cancellation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ι → ℝ) (M : ι → κ → ℝ) (v : κ → ℝ)
    (h : ∀ j, ∑ i, q i*M i j = 0) :
    ∑ i, q i*(∑ j, M i j*v j) = 0 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, h, zero_mul, Finset.sum_const_zero]

theorem power_residual_bound (e h h0 B : ℝ) (m : ℕ)
    (hh : 0 < h0) (hf : h0 ≤ |h|) (hb : |e^m*h| ≤ B) :
    |e|^m ≤ B/h0 := by
  simpa only [abs_pow] using residual_bound (e^m) h h0 B hh hf hb

end ACRZeroDivisors
