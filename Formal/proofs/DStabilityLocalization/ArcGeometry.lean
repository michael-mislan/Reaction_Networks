import proofs.DStabilityLocalization.Star

/-!
# Geometry of one channel at an eigenvalue `z`

Compact rational parametrization of a first-order piece at the eigenvalue `z`:
`val z s = (1 - s) / (1 - s + s z)`, `s ∈ [0,1]`; `s = 0` is the fast (static) end, `s = 1`
the slow (removed) end, and for `0 < s < 1` the piece has inverse rate `t = s / (1 - s)`
(`val z s = 1 / (1 + z t)`).  Throughout, `z` is non-real (`z.im ≠ 0`); `0 ≤ z.re` is added
where positivity is needed.

* `sync_det`: the Jacobian determinant of two pieces is
  `2 r_j r_k |z|² (Im z) (A_j A_k + Y_j Y_k) (s_j - s_k) / (m_j² m_k²)`, where
  `A = 1 - s + s Re z`, `Y = s Im z`, `m = A² + Y² = |1 - s + s z|²`; for `Re z ≥ 0` the tangents
  are collinear iff the parameters are equal (any signs of the loads).
* `open_two_pieces`: at two unequal interior parameters the two-piece map is open
  (inverse function theorem with a surjective derivative).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Complex Filter Topology
open scoped BigOperators

namespace DStabilityLocalization

/-- Arc parametrization of a unit load at the eigenvalue `z`. -/
def val (z : ℂ) (s : ℝ) : ℂ := (1 - (s : ℂ)) / (1 - (s : ℂ) + (s : ℂ) * z)

/-- Real part of the denominator `1 - s + s z`. -/
def dre (z : ℂ) (s : ℝ) : ℝ := 1 - s + s * z.re

/-- Imaginary part of the denominator `1 - s + s z`. -/
def dim (z : ℂ) (s : ℝ) : ℝ := s * z.im

/-- `msq z s = |1 - s + s z|²`. -/
def msq (z : ℂ) (s : ℝ) : ℝ := dre z s ^ 2 + dim z s ^ 2

theorem den_eq (z : ℂ) (s : ℝ) :
    1 - (s : ℂ) + (s : ℂ) * z = (dre z s : ℂ) + (dim z s : ℂ) * I := by
  apply Complex.ext <;> simp [dre, dim]

theorem val_den_ne {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) : 1 - (s : ℂ) + (s : ℂ) * z ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  rcases h2 with h2 | h2
  · subst h2; simp at h1
  · exact hz h2

theorem msq_pos {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) : 0 < msq z s := by
  have hne := val_den_ne hz s
  rw [den_eq] at hne
  unfold msq
  by_contra hle
  have h1 : dre z s = 0 := by nlinarith [sq_nonneg (dre z s), sq_nonneg (dim z s)]
  have h2 : dim z s = 0 := by nlinarith [sq_nonneg (dre z s), sq_nonneg (dim z s)]
  apply hne
  rw [h1, h2]; simp

theorem val_zero (z : ℂ) : val z 0 = 1 := by simp [val]

theorem val_one (z : ℂ) : val z 1 = 0 := by simp [val]

/-- For a positive inverse rate `t` and `Re z ≥ 0`, the lag factor `1/(1+zt)` is
`val z (t/(1+t))`. -/
theorem lag_eq_val {z : ℂ} (hre : 0 ≤ z.re) (t : ℝ) (ht : 0 < t) :
    (1 : ℂ) / (1 + z * (t : ℂ)) = val z (t / (1 + t)) := by
  have h1 : (1 + t : ℝ) ≠ 0 := by linarith
  have h1c : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast h1
  have hd : (1 : ℂ) + z * t ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; nlinarith
  unfold val
  have hc : ((t / (1 + t) : ℝ) : ℂ) = (t : ℂ) / (1 + (t : ℂ)) := by push_cast; ring
  rw [hc]
  have hden : 1 - (t : ℂ) / (1 + (t : ℂ)) + (t : ℂ) / (1 + (t : ℂ)) * z =
      (1 + z * t) / (1 + (t : ℂ)) := by
    field_simp; ring
  have hnum : 1 - (t : ℂ) / (1 + (t : ℂ)) = 1 / (1 + (t : ℂ)) := by
    field_simp; ring
  rw [hden, hnum]
  field_simp

/-- Inverse: an interior parameter is the lag factor of the inverse rate `s/(1-s)`. -/
theorem val_eq_lag {z : ℂ} (hre : 0 ≤ z.re) (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    val z s = 1 / (1 + z * ((s / (1 - s) : ℝ) : ℂ)) := by
  have ht : 0 < s / (1 - s) := div_pos h0 (by linarith)
  rw [lag_eq_val hre _ ht]
  congr 1
  have : (1 - s) ≠ 0 := by linarith
  field_simp
  ring

theorem continuous_val {z : ℂ} (hz : z.im ≠ 0) : Continuous (val z) := by
  unfold val
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s; exact val_den_ne hz s

/-- The derivative of `val z`, written with real and imaginary parts:
`-z / (1 - s + s z)²`. -/
def dval (z : ℂ) (s : ℝ) : ℂ :=
  ((-(z.re * (dre z s ^ 2 - dim z s ^ 2) + 2 * dre z s * dim z s * z.im) : ℝ) +
    ((-(z.im * (dre z s ^ 2 - dim z s ^ 2) - 2 * dre z s * dim z s * z.re)) : ℝ) * I) /
    ((msq z s) ^ 2 : ℝ)

theorem dval_eq {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    dval z s = -z / (1 - (s : ℂ) + (s : ℂ) * z) ^ 2 := by
  have hden := pow_ne_zero 2 (val_den_ne hz s)
  rw [eq_div_iff hden]
  have hm : 0 < msq z s := msq_pos hz s
  have hmne : ((msq z s ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (pow_pos hm 2))
  unfold dval
  rw [div_mul_eq_mul_div, div_eq_iff hmne, den_eq]
  apply Complex.ext <;>
    simp [msq, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem hasStrictDerivAt_val {z : ℂ} (hz : z.im ≠ 0) (s : ℝ) :
    HasStrictDerivAt (val z) (dval z s) s := by
  have hx : HasStrictDerivAt (fun x : ℝ => (x : ℂ)) 1 s := by
    simpa using (Complex.ofRealCLM.hasStrictDerivAt (x := s))
  have hN : HasStrictDerivAt (fun x : ℝ => 1 - (x : ℂ)) (-1) s := by
    simpa using hx.const_sub 1
  have hD : HasStrictDerivAt (fun x : ℝ => 1 - (x : ℂ) + (x : ℂ) * z) (-1 + z) s := by
    simpa using (hx.const_sub (1 : ℂ)).add (hx.mul_const z)
  have h := hN.div hD (val_den_ne hz s)
  convert h using 1
  rw [dval_eq hz]
  congr 1
  ring

/-- **Synchronization identity at `z`.** -/
theorem sync_det {z : ℂ} (hz : z.im ≠ 0) (rj rk sj sk : ℝ) :
    (rj * (dval z sj)).re * (rk * (dval z sk)).im - (rj * (dval z sj)).im * (rk * (dval z sk)).re
      = 2 * rj * rk * (z.re ^ 2 + z.im ^ 2) * z.im *
          (dre z sj * dre z sk + dim z sj * dim z sk) * (sj - sk) /
          ((msq z sj) ^ 2 * (msq z sk) ^ 2) := by
  have hj := ne_of_gt (pow_pos (msq_pos hz sj) 2)
  have hk := ne_of_gt (pow_pos (msq_pos hz sk) 2)
  simp only [dval, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.normSq_ofReal, mul_zero, sub_zero, zero_mul, mul_one, add_zero,
    zero_add, zero_div]
  field_simp
  simp only [msq, dre, dim]
  ring

theorem sync_det_ne {z : ℂ} (hre : 0 ≤ z.re) (hz : z.im ≠ 0) {rj rk sj sk : ℝ}
    (hrj : rj ≠ 0) (hrk : rk ≠ 0)
    (hj0 : 0 < sj) (hj1 : sj < 1) (hk0 : 0 < sk) (hk1 : sk < 1) (hne : sj ≠ sk) :
    (rj * (dval z sj)).re * (rk * (dval z sk)).im - (rj * (dval z sj)).im * (rk * (dval z sk)).re
      ≠ 0 := by
  rw [sync_det hz]
  have hAj : 0 < dre z sj := by unfold dre; nlinarith [mul_nonneg hj0.le hre]
  have hAk : 0 < dre z sk := by unfold dre; nlinarith [mul_nonneg hk0.le hre]
  have hP : 0 < dre z sj * dre z sk + dim z sj * dim z sk := by
    have : 0 ≤ dim z sj * dim z sk := by
      unfold dim
      have := mul_nonneg (mul_nonneg hj0.le hk0.le) (sq_nonneg z.im)
      nlinarith
    nlinarith [mul_pos hAj hAk]
  have hz2 : 0 < z.re ^ 2 + z.im ^ 2 := by
    have := pow_pos (abs_pos.mpr hz) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg z.re]
  have hden := mul_pos (pow_pos (msq_pos hz sj) 2) (pow_pos (msq_pos hz sk) 2)
  apply div_ne_zero _ (ne_of_gt hden)
  have := sub_ne_zero.mpr hne
  have h2 : (2 : ℝ) * rj * rk * (z.re ^ 2 + z.im ^ 2) * z.im ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hrj) hrk)
      (ne_of_gt hz2)) hz
  exact mul_ne_zero (mul_ne_zero h2 (ne_of_gt hP)) this

/-- 2×2 Cramer: two ℝ-independent complex numbers span `ℂ` over `ℝ`. -/
theorem real_span_of_det_ne {a b : ℂ} (h : a.re * b.im - a.im * b.re ≠ 0) (w : ℂ) :
    ∃ x y : ℝ, (x : ℂ) * a + (y : ℂ) * b = w := by
  set Δ := a.re * b.im - a.im * b.re
  refine ⟨(w.re * b.im - w.im * b.re) / Δ, (a.re * w.im - a.im * w.re) / Δ, ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    field_simp
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    field_simp
    ring

/-- **Openness at two unequal interior parameters.** The two-piece map
`(x, y) ↦ c₀ + r_j val z x + r_k val z y` sends every neighbourhood of `(s_j, s_k)` onto a
neighbourhood of its value. -/
theorem open_two_pieces {z : ℂ} (hre : 0 ≤ z.re) (hz : z.im ≠ 0) (c₀ : ℂ) {rj rk sj sk : ℝ}
    (hrj : rj ≠ 0) (hrk : rk ≠ 0)
    (hj0 : 0 < sj) (hj1 : sj < 1) (hk0 : 0 < sk) (hk1 : sk < 1) (hne : sj ≠ sk) :
    map (fun p : ℝ × ℝ => c₀ + (rj : ℂ) * val z p.1 + (rk : ℂ) * val z p.2) (𝓝 (sj, sk)) =
      𝓝 (c₀ + (rj : ℂ) * val z sj + (rk : ℂ) * val z sk) := by
  set Lj : ℝ × ℝ →L[ℝ] ℂ :=
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (dval z sj)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ))
  set Lk : ℝ × ℝ →L[ℝ] ℂ :=
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (dval z sk)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℝ))
  have hj : HasStrictFDerivAt (fun p : ℝ × ℝ => val z p.1) Lj (sj, sk) :=
    (hasStrictDerivAt_val hz sj).hasStrictFDerivAt.comp (sj, sk) hasStrictFDerivAt_fst
  have hk : HasStrictFDerivAt (fun p : ℝ × ℝ => val z p.2) Lk (sj, sk) :=
    (hasStrictDerivAt_val hz sk).hasStrictFDerivAt.comp (sj, sk) hasStrictFDerivAt_snd
  have hF : HasStrictFDerivAt
      (fun p : ℝ × ℝ => c₀ + (rj : ℂ) * val z p.1 + (rk : ℂ) * val z p.2)
      ((rj : ℂ) • Lj + (rk : ℂ) • Lk) (sj, sk) := by
    have := ((hj.const_smul (rj : ℂ)).add (hk.const_smul (rk : ℂ))).const_add c₀
    convert this using 1
    funext p
    simp [add_assoc]
  apply hF.map_nhds_eq_of_surj
  rw [LinearMap.range_eq_top]
  intro w
  obtain ⟨x, y, hxy⟩ := real_span_of_det_ne
    (sync_det_ne hre hz hrj hrk hj0 hj1 hk0 hk1 hne) w
  refine ⟨(x, y), ?_⟩
  rw [← hxy]
  simp [Lj, Lk, Complex.real_smul]; ring

end DStabilityLocalization
