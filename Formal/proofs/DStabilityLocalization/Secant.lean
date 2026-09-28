import proofs.DStabilityLocalization.Star

/-!
# The secant inequality on the closed right half-plane (Lemmas 7.1, 7.2)

If `Re z ≥ 0`, `τ_j > 0` and `∏_{j ∈ s} (1 + z τ_j) = -g` with `g > 0`, then `|s| ≥ 3` and
`g · cos(π/|s|)^|s| ≥ 1`, i.e. `g ≥ sec(π/N)^N` (Thron; Tyson–Othmer).  Moreover
`N ↦ cos(π/N)^N` is strictly increasing for `N ≥ 3`, so the secant thresholds decrease.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Complex Set Real
open scoped BigOperators

namespace DStabilityLocalization

theorem strictConcaveOn_logCos :
    StrictConcaveOn ℝ (Ioo (-(π / 2)) (π / 2)) (fun x => Real.log (Real.cos x)) := by
  have hcos : ∀ x ∈ Ioo (-(π / 2)) (π / 2), 0 < Real.cos x :=
    fun x hx => Real.cos_pos_of_mem_Ioo hx
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioo _ _)
  · exact ContinuousOn.log (Real.continuous_cos.continuousOn) (fun x hx => (hcos x hx).ne')
  · rw [interior_Ioo]
    have hder : ∀ x ∈ Ioo (-(π / 2)) (π / 2),
        deriv (fun x => Real.log (Real.cos x)) x = -Real.tan x := by
      intro x hx
      have h := (Real.hasDerivAt_cos x).log (hcos x hx).ne'
      rw [h.deriv, Real.tan_eq_sin_div_cos]
      ring
    intro x hx y hy hxy
    rw [hder x hx, hder y hy]
    have := Real.strictMonoOn_tan hx hy hxy
    linarith

/-- Jensen + monotonicity: `∏ cos φ_j ≤ cos(π/N)^N` when `φ_j ∈ [0, π/2)` and `Σ φ_j ≥ π`. -/
theorem prod_cos_le {α : Type*} (s : Finset α) (φ : α → ℝ)
    (h0 : ∀ j ∈ s, 0 ≤ φ j) (h1 : ∀ j ∈ s, φ j < π / 2) (hsum : π ≤ ∑ j ∈ s, φ j) :
    (∏ j ∈ s, Real.cos (φ j)) ≤ Real.cos (π / s.card) ^ s.card := by
  classical
  have hne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · rw [h, Finset.sum_empty] at hsum; linarith [Real.pi_pos]
    · exact h
  set N : ℕ := s.card with hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Finset.card_pos.mpr hne
  set μ : ℝ := (∑ j ∈ s, φ j) / N with hμ
  have hμlo : π / N ≤ μ := by rw [hμ]; exact div_le_div_of_nonneg_right hsum hNpos.le
  have hμhi : μ < π / 2 := by
    rw [hμ, div_lt_iff₀ hNpos]
    calc ∑ j ∈ s, φ j < ∑ j ∈ s, π / 2 := Finset.sum_lt_sum_of_nonempty hne h1
      _ = π / 2 * N := by rw [Finset.sum_const, nsmul_eq_mul, hN]; ring
  have hpiN : 0 < π / N := div_pos Real.pi_pos hNpos
  have hcosφ : ∀ j ∈ s, 0 < Real.cos (φ j) := fun j hj =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [h0 j hj, Real.pi_pos], h1 j hj⟩
  -- Jensen for the concave `log ∘ cos`
  have hJ := (strictConcaveOn_logCos.concaveOn).le_map_sum (t := s) (w := fun _ => (1 : ℝ) / N)
    (p := φ) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul, ← hN]; field_simp)
    (fun j hj => ⟨by linarith [h0 j hj, Real.pi_pos], h1 j hj⟩)
  simp only [smul_eq_mul] at hJ
  have hmean : (∑ j ∈ s, 1 / (N : ℝ) * φ j) = μ := by
    rw [← Finset.mul_sum, hμ]; ring
  rw [hmean] at hJ
  -- `log cos` is antitone on `[0, π/2)`
  have hmono : Real.log (Real.cos μ) ≤ Real.log (Real.cos (π / N)) := by
    apply Real.log_le_log (Real.cos_pos_of_mem_Ioo ⟨by linarith, hμhi⟩)
    apply Real.cos_le_cos_of_nonneg_of_le_pi hpiN.le (by linarith [Real.pi_pos]) hμlo
  have hsumlog : (∑ j ∈ s, Real.log (Real.cos (φ j))) ≤ N * Real.log (Real.cos (π / N)) := by
    have : (∑ j ∈ s, 1 / (N : ℝ) * Real.log (Real.cos (φ j))) =
        (1 / N) * ∑ j ∈ s, Real.log (Real.cos (φ j)) := by rw [Finset.mul_sum]
    rw [this] at hJ
    have h2 := hJ.trans hmono
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hNpos] at h2
    linarith
  have hprod : (∏ j ∈ s, Real.cos (φ j)) = Real.exp (∑ j ∈ s, Real.log (Real.cos (φ j))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl (fun j hj => (Real.exp_log (hcosφ j hj)).symm)
  have hcosN : 0 < Real.cos (π / N) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rw [hprod, show Real.cos (π / N) ^ N = Real.exp (N * Real.log (Real.cos (π / N))) by
    rw [Real.exp_nat_mul, Real.exp_log hcosN]]
  exact Real.exp_le_exp.mpr hsumlog

/-- **Secant inequality (Lemma 7.1)** on the closed right half-plane. -/
theorem secant_inequality {α : Type*} (s : Finset α) (τ : α → ℝ) (hτ : ∀ j ∈ s, 0 < τ j)
    (z : ℂ) (hz : 0 ≤ z.re) (g : ℝ) (hg : 0 < g)
    (hprod : ∏ j ∈ s, (1 + z * (τ j : ℂ)) = -(g : ℂ)) :
    3 ≤ s.card ∧ 1 ≤ g * Real.cos (π / s.card) ^ s.card := by
  classical
  set a : α → ℂ := fun j => 1 + z * (τ j : ℂ) with ha
  have hre : ∀ j ∈ s, 1 ≤ (a j).re := by
    intro j hj; simp only [ha, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    linarith [mul_nonneg hz (hτ j hj).le]
  have hne0 : ∀ j ∈ s, a j ≠ 0 := fun j hj h => by
    have := hre j hj; rw [h, Complex.zero_re] at this; linarith
  set θ : α → ℝ := fun j => Complex.arg (a j) with hθ
  have hθlt : ∀ j ∈ s, |θ j| < π / 2 := fun j hj =>
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith [hre j hj]))
  -- polar form of the product
  have hpolar : (∏ j ∈ s, ((‖a j‖ : ℝ) : ℂ)) * Complex.exp ((∑ j ∈ s, θ j : ℝ) * I) =
      -(g : ℂ) := by
    rw [← hprod]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => Complex.norm_mul_exp_arg_mul_I (a j))
  have hnormprod : (∏ j ∈ s, ‖a j‖) = g := by
    have h := congrArg (fun w : ℂ => ‖w‖) hpolar
    simp only [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs, norm_neg,
      Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos hg] at h
    rw [← h]
    exact Finset.prod_congr rfl (fun j _ => (abs_of_nonneg (norm_nonneg _)).symm)
  have hPpos : (0 : ℝ) < ∏ j ∈ s, ‖a j‖ := by rw [hnormprod]; exact hg
  have hexp : Complex.exp ((∑ j ∈ s, θ j : ℝ) * I) = -1 := by
    have hcast : (∏ j ∈ s, ((‖a j‖ : ℝ) : ℂ)) = (g : ℂ) := by
      rw [← Complex.ofReal_prod, hnormprod]
    rw [hcast] at hpolar
    have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    have e : Complex.exp ((∑ j ∈ s, θ j : ℝ) * I) =
        ((g : ℂ) * Complex.exp ((∑ j ∈ s, θ j : ℝ) * I)) / g := by field_simp
    rw [e, hpolar]
    field_simp
  -- the angle sum is an odd multiple of π
  have hodd : π ≤ |∑ j ∈ s, θ j| := by
    have h1 : Complex.exp ((∑ j ∈ s, θ j : ℝ) * I - π * I) = 1 := by
      rw [Complex.exp_sub, hexp, show (π : ℂ) * I = (π : ℂ) * I from rfl,
        Complex.exp_pi_mul_I]; norm_num
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    have hre' : (∑ j ∈ s, θ j) - π = n * (2 * π) := by
      have := congrArg Complex.im hn
      simp at this
      linarith
    have hS : (∑ j ∈ s, θ j) = (2 * n + 1) * π := by linarith
    rw [hS, abs_mul, abs_of_pos Real.pi_pos]
    have : (1 : ℝ) ≤ |2 * (n : ℝ) + 1| := by
      rcases le_or_gt 0 n with h | h
      · have h' : (0 : ℝ) ≤ n := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast (Int.le_sub_one_of_lt h)
        rw [abs_of_neg (by linarith)]; linarith
    calc π = 1 * π := by ring
      _ ≤ |2 * (n : ℝ) + 1| * π := mul_le_mul_of_nonneg_right this Real.pi_pos.le
  -- all angles have the sign of `Im z`
  have hsum_abs : (∑ j ∈ s, |θ j|) = |∑ j ∈ s, θ j| := by
    rcases le_or_gt 0 z.im with him | him
    · have hnn : ∀ j ∈ s, 0 ≤ θ j := fun j hj => Complex.arg_nonneg_iff.mpr (by
        simp only [ha, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_add]
        exact mul_nonneg him (hτ j hj).le)
      rw [abs_of_nonneg (Finset.sum_nonneg hnn)]
      exact Finset.sum_congr rfl (fun j hj => abs_of_nonneg (hnn j hj))
    · have hnp : ∀ j ∈ s, θ j < 0 := fun j hj => Complex.arg_neg_iff.mpr (by
        simp only [ha, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, zero_add]
        exact mul_neg_of_neg_of_pos him (hτ j hj))
      have hsneg : (∑ j ∈ s, θ j) ≤ 0 := Finset.sum_nonpos (fun j hj => (hnp j hj).le)
      rw [abs_of_nonpos hsneg, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun j hj => abs_of_neg (hnp j hj))
  have hφsum : π ≤ ∑ j ∈ s, |θ j| := by rw [hsum_abs]; exact hodd
  have hcard : 3 ≤ s.card := by
    by_contra hlt
    push Not at hlt
    have hle : (s.card : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
    have : (∑ j ∈ s, |θ j|) < π := by
      rcases Finset.eq_empty_or_nonempty s with he | hne
      · rw [he, Finset.sum_empty]; exact Real.pi_pos
      · calc (∑ j ∈ s, |θ j|) < ∑ j ∈ s, π / 2 := Finset.sum_lt_sum_of_nonempty hne hθlt
          _ = π / 2 * s.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ π / 2 * 2 := mul_le_mul_of_nonneg_left hle (by linarith [Real.pi_pos])
          _ = π := by ring
    linarith
  refine ⟨hcard, ?_⟩
  have hcos : (∏ j ∈ s, Real.cos (|θ j|)) ≤ Real.cos (π / s.card) ^ s.card :=
    prod_cos_le s (fun j => |θ j|) (fun j _ => abs_nonneg _) hθlt hφsum
  have hre_prod : (1 : ℝ) ≤ ∏ j ∈ s, ‖a j‖ * Real.cos (|θ j|) := by
    have : ∀ j ∈ s, ‖a j‖ * Real.cos (|θ j|) = (a j).re := by
      intro j hj
      rw [Real.cos_abs, hθ, Complex.cos_arg (hne0 j hj)]
      field_simp [norm_ne_zero_iff.mpr (hne0 j hj)]
    rw [Finset.prod_congr rfl this]
    calc (1 : ℝ) = ∏ j ∈ s, (1 : ℝ) := by simp
      _ ≤ ∏ j ∈ s, (a j).re :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j hj => hre j hj)
  rw [Finset.prod_mul_distrib, hnormprod] at hre_prod
  calc (1 : ℝ) ≤ g * ∏ j ∈ s, Real.cos (|θ j|) := hre_prod
    _ ≤ g * Real.cos (π / s.card) ^ s.card := mul_le_mul_of_nonneg_left hcos hg.le

/-- **Window (Lemma 7.2).** `N ↦ cos(π/N)^N` is strictly increasing for `N ≥ 3`. -/
theorem cos_pow_strictMono {M N : ℕ} (hM : 3 ≤ M) (hMN : M < N) :
    Real.cos (π / M) ^ M < Real.cos (π / N) ^ N := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hconv : StrictConvexOn ℝ (Ioo (-(π / 2)) (π / 2))
      (fun x => -Real.log (Real.cos x)) := strictConcaveOn_logCos.neg
  set x := π / N
  set y := π / M
  have hxy : x < y := by
    apply div_lt_div_of_pos_left Real.pi_pos hMpos (by exact_mod_cast hMN)
  have hx0 : 0 < x := div_pos Real.pi_pos hNpos
  have hy2 : y < π / 2 := by
    apply div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hmem : ∀ w, 0 ≤ w → w < π / 2 → w ∈ Ioo (-(π / 2)) (π / 2) :=
    fun w h0 h1 => ⟨by linarith [Real.pi_pos], h1⟩
  have hsec := hconv.secant_strict_mono (a := 0) (x := x) (y := y)
    (hmem 0 le_rfl (by linarith [Real.pi_pos])) (hmem x hx0.le (by linarith))
    (hmem y (by linarith) hy2) hx0.ne' (by linarith) hxy
  simp only [Real.cos_zero, Real.log_one, neg_zero, sub_zero] at hsec
  -- `-log cos x / x < -log cos y / y` means `M log cos y < N log cos x`
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo (hmem x hx0.le (by linarith))
  have hcy : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo (hmem y (by linarith) hy2)
  have hlog : (M : ℝ) * Real.log (Real.cos y) < N * Real.log (Real.cos x) := by
    have hπ := Real.pi_pos
    have ex : -Real.log (Real.cos x) / x = -((N : ℝ) * Real.log (Real.cos x)) / π := by
      simp only [x]; field_simp
    have ey : -Real.log (Real.cos y) / y = -((M : ℝ) * Real.log (Real.cos y)) / π := by
      simp only [y]; field_simp
    rw [ex, ey, div_lt_div_iff_of_pos_right hπ] at hsec
    linarith
  have e1 : Real.cos y ^ M = Real.exp (M * Real.log (Real.cos y)) := by
    rw [Real.exp_nat_mul, Real.exp_log hcy]
  have e2 : Real.cos x ^ N = Real.exp (N * Real.log (Real.cos x)) := by
    rw [Real.exp_nat_mul, Real.exp_log hcx]
  rw [e1, e2]
  exact Real.exp_lt_exp.mpr hlog

end DStabilityLocalization
