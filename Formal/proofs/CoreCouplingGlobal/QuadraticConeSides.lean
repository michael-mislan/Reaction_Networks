import proofs.CoreCouplingGlobal.SaddleQuadratic

namespace CoreCouplingGlobal

/-- Completing the H square isolates the strictly positive z curvature on b=0. -/
theorem quadratic_B_plane_identity (B z m w ζ η r : ℝ)
    (hw : w ≠ 0) (hz : 16+4*z ≠ 0) :
    responseQuadratic B z m w (3/((16+4*z)*w)) 0 ζ η r =
      (3*(20001/10000)/(2*(16+4*z)*w))*(η-(16+4*z)/(20001/10000)*ζ)^2+
      (B-159984/20001+(40008/20001)*z)/(2*w)*ζ^2+r^2/2 := by
  unfold responseQuadratic
  have hz' : 16+z*4 ≠ 0 := by simpa only [mul_comm] using hz
  field_simp
  ring

theorem quadratic_B_plane_nonnegative (B z m w ζ η r : ℝ)
    (hB : 8 ≤ B) (hz : 0 ≤ z) (hw : 0 < w) :
    0 ≤ responseQuadratic B z m w (3/((16+4*z)*w)) 0 ζ η r := by
  rw [quadratic_B_plane_identity B z m w ζ η r (ne_of_gt hw) (by positivity)]
  have hc : 0 ≤ B-159984/20001+(40008/20001)*z := by linarith
  positivity

theorem quadratic_B_plane_positive (B z m w ζ η r : ℝ)
    (hB : 8 ≤ B) (hz : 0 ≤ z) (hw : 0 < w)
    (hn : ζ ≠ 0 ∨ η ≠ 0 ∨ r ≠ 0) :
    0 < responseQuadratic B z m w (3/((16+4*z)*w)) 0 ζ η r := by
  rw [quadratic_B_plane_identity B z m w ζ η r (ne_of_gt hw) (by positivity)]
  have hc : 0 < (B-159984/20001+(40008/20001)*z)/(2*w) :=
    div_pos (by linarith) (by positivity)
  have hH : 0 < 3*(20001/10000:ℝ)/(2*(16+4*z)*w) := by positivity
  have hHsq := mul_nonneg hH.le (sq_nonneg (η-(16+4*z)/(20001/10000)*ζ))
  have hzsq := mul_nonneg hc.le (sq_nonneg ζ)
  rcases eq_or_ne ζ 0 with hζ | hζ
  · subst ζ
    simp only [mul_zero,sub_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero] at *
    rcases hn with hn | hn | hn
    · exact False.elim (hn rfl)
    · have hh := mul_pos hH (sq_pos_of_ne_zero hn)
      nlinarith [sq_nonneg r]
    · nlinarith [sq_pos_of_ne_zero hn]
  · have hh := mul_pos hc (sq_pos_of_ne_zero hζ)
    nlinarith [sq_nonneg r]

/-- A negative cone cannot meet the hyperplane of zero B displacement. -/
theorem negative_quadratic_B_ne_zero (B z m w b ζ η r : ℝ)
    (hB : 8 ≤ B) (hz : 0 ≤ z) (hw : 0 < w)
    (hq : responseQuadratic B z m w (3/((16+4*z)*w)) b ζ η r < 0) : b ≠ 0 := by
  intro hb
  rw [hb] at hq
  have hn := quadratic_B_plane_nonnegative B z m w ζ η r hB hz hw
  linarith

end CoreCouplingGlobal
