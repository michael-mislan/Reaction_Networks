import proofs.TypeII3.Algebra.TransferMap

namespace TypeIIL

open TypeII3

/-- The transfer denominator is positive at every positive root without
requiring `B>0`.  The invariant actually needed is the positive cross
determinant `A*b+a*B`; it orders the numerator zero before the denominator
pole. -/
theorem denominator_pos_of_root_cross
    {A B lam a b t xPrev x : ℝ} {m : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcross : 0 < A * b + a * B)
    (hxPrev : 0 < xPrev) (hx : 0 < x)
    (hroot :
      (A - lam * t ^ m * a) * xPrev =
        (B + lam * b * t ^ m) * x) :
    0 < A - lam * t ^ m * a := by
  let den := A - lam * t ^ m * a
  let num := B + lam * b * t ^ m
  have hidentity : A * b + a * B = b * den + a * num := by
    dsimp [den, num]
    ring
  by_contra hnot
  have hden : den ≤ 0 := le_of_not_gt hnot
  have hleft : den * xPrev ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hden (le_of_lt hxPrev)
  have hright : num * x ≤ 0 := by
    rw [← hroot]
    exact hleft
  have hnum : num ≤ 0 :=
    nonpos_of_mul_nonpos_right (by simpa [mul_comm] using hright) hx
  have hbden : b * den ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) hden
  have hanum : a * num ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hnum
  rw [hidentity] at hcross
  linarith

/-- Positivity of the secant transfer gain under the same cross-determinant
condition.  Neither `A` nor `B` needs an individual sign assumption. -/
theorem transferGain_pos_cross
    {A B lam a b r s : ℝ} {m : ℕ}
    (hlam : 0 < lam) (hcross : 0 < A * b + a * B)
    (hr : 0 < r) (hs : 0 < s) (hm : 0 < m)
    (hdenr : 0 < A - lam * r ^ m * a)
    (hdens : 0 < A - lam * s ^ m * a) :
    0 < transferGain A B lam a b r s m := by
  rw [transferGain]
  have hsec : 0 < secantPoly r s m := secantPoly_pos hr hs hm
  positivity

end TypeIIL
