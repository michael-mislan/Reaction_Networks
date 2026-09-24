import proofs.TypeII3.Algebra.PowSecant

namespace TypeII3

noncomputable def transfer (A B lam a b : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (B + lam * b * t ^ m) / (A - lam * t ^ m * a)

noncomputable def transferGain (A B lam a b r s : ℝ) (m : ℕ) : ℝ :=
  lam * (A * b + a * B) * secantPoly r s m /
    ((A - lam * r ^ m * a) * (A - lam * s ^ m * a))

theorem denominator_pos_of_root
    {A B lam a b t xPrev x : ℝ} {m : ℕ}
    (hB : 0 < B) (hlam : 0 < lam) (hb : 0 < b)
    (ht : 0 < t) (hxPrev : 0 < xPrev) (hx : 0 < x)
    (hroot :
      (A - lam * t ^ m * a) * xPrev =
        (B + lam * b * t ^ m) * x) :
    0 < A - lam * t ^ m * a := by
  have hpow : 0 < t ^ m := pow_pos ht m
  have hrhs : 0 < (B + lam * b * t ^ m) * x := by positivity
  have hprod : 0 < (A - lam * t ^ m * a) * xPrev := by
    rw [hroot]
    exact hrhs
  nlinarith

theorem transfer_difference
    {A B lam a b r s : ℝ} {m : ℕ}
    (hdenr : A - lam * r ^ m * a ≠ 0)
    (hdens : A - lam * s ^ m * a ≠ 0) :
    transfer A B lam a b m r - transfer A B lam a b m s =
      transferGain A B lam a b r s m * (r - s) := by
  have hpow := pow_sub_pow_eq_mul_secantPoly r s m
  unfold transfer transferGain
  rw [div_sub_div _ _ hdenr hdens]
  have hnum :
      (B + lam * b * r ^ m) * (A - lam * s ^ m * a) -
          (A - lam * r ^ m * a) * (B + lam * b * s ^ m) =
        lam * (A * b + a * B) * (r ^ m - s ^ m) := by
    ring
  rw [hnum, hpow]
  ring

theorem transferGain_pos
    {A B lam a b r s : ℝ} {m : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hlam : 0 < lam)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hs : 0 < s)
    (hm : 0 < m)
    (hdenr : 0 < A - lam * r ^ m * a)
    (hdens : 0 < A - lam * s ^ m * a) :
    0 < transferGain A B lam a b r s m := by
  rw [transferGain]
  have hsec : 0 < secantPoly r s m := secantPoly_pos hr hs hm
  positivity

theorem ratio_eq_transfer_of_root
    {A B lam a b t xPrev x : ℝ} {m : ℕ}
    (hx : 0 < x) (hden : 0 < A - lam * t ^ m * a)
    (hroot :
      (A - lam * t ^ m * a) * xPrev =
        (B + lam * b * t ^ m) * x) :
    xPrev / x = transfer A B lam a b m t := by
  unfold transfer
  apply (div_eq_div_iff (ne_of_gt hx) (ne_of_gt hden)).2
  simpa [mul_comm] using hroot

theorem comparison_equation
    {K e f xPrev x xNext yPrev y yNext : ℝ}
    (hx : 0 < x) (hyPrev : 0 < yPrev) (hy : 0 < y)
    (hyNext : 0 < yNext)
    (hdiff :
      xPrev / x - yPrev / y =
        K * ((e * x + f * xNext) - (e * y + f * yNext))) :
    xPrev / yPrev - 1 =
      (1 + K * e * (x / y) * y ^ 2 / yPrev) * (x / y - 1) +
      (K * f * (x / y) * y * yNext / yPrev) * (xNext / yNext - 1) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hyp0 : yPrev ≠ 0 := ne_of_gt hyPrev
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hyn0 : yNext ≠ 0 := ne_of_gt hyNext
  calc
    xPrev / yPrev - 1 =
        (x / y - 1) + x / yPrev * (xPrev / x - yPrev / y) := by
          field_simp [hx0, hyp0, hy0]
          ring
    _ = (x / y - 1) + x / yPrev *
        (K * ((e * x + f * xNext) - (e * y + f * yNext))) := by rw [hdiff]
    _ = (1 + K * e * (x / y) * y ^ 2 / yPrev) * (x / y - 1) +
        (K * f * (x / y) * y * yNext / yPrev) * (xNext / yNext - 1) := by
          field_simp [hx0, hyp0, hy0, hyn0]
          ring

end TypeII3
