import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace RandomViability.Binding
open scoped BigOperators

/-- Lower Taylor bound, valid also for negative jumps. -/
theorem log_one_add_lower (s : ℝ) (hs : -(1/2) ≤ s) :
    s-2*s^2 ≤ Real.log (1+s) := by
  have hp : 0 < 1+s := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hp
  have hi : (s-2*s^2) ≤ 1-(1+s)⁻¹ := by
    apply (mul_le_mul_iff_of_pos_right hp).mp
    have he : (1-(1+s)⁻¹)*(1+s) = s := by field_simp; ring
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ 1+2*s by linarith)]
  exact hi.trans h

theorem log_jump_lower (Y d : ℝ) (hY : 0 < Y) (hd : -Y/2 ≤ d) :
    d/Y-2*d^2/Y^2 ≤ Real.log (Y+d)-Real.log Y := by
  have hs : -(1/2) ≤ d/Y := (le_div_iff₀ hY).2 (by linarith)
  have h := log_one_add_lower (d/Y) hs
  have hp : 0 < Y+d := by linarith
  rw [show 1+d/Y = (Y+d)/Y by field_simp,
    Real.log_div hp.ne' hY.ne'] at h
  convert h using 1
  ring

/-- Exact generator inequality for arbitrary finite reaction channels. This
has no probability or independence assumption; rates and jumps are literal. -/
theorem generator_log_lower {ι : Type*} [Fintype ι]
    (rate jump : ι → ℝ) (Y : ℝ) (hY : 0 < Y)
    (hr : ∀ i, 0 ≤ rate i) (hj : ∀ i, -Y/2 ≤ jump i) :
    (∑ i, rate i*jump i)/Y - 2*(∑ i,rate i*(jump i)^2)/Y^2 ≤
      ∑ i,rate i*(Real.log (Y+jump i)-Real.log Y) := by
  calc
    _ = ∑ i,rate i*(jump i/Y-2*(jump i)^2/Y^2) := by
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (log_jump_lower Y (jump i) hY (hj i)) (hr i)

end RandomViability.Binding
