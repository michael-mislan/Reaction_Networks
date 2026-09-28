import proofs.DStabilityLocalization.RealEigenvalues

/-!
# The criterion is not an equivalence

The star with core `[[-1,-1],[1,0]]`, one coordinate channel at the first coordinate and one
piece of load `1` is D-stable, although its all-static boundary system (core `[[0,-1],[1,0]]`)
has the eigenvalue `i` at unit scaling.  So "every boundary system D-stable" is sufficient but
not necessary for D-stability of the star; only D-semistability localizes exactly.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

/-- Core of the example. -/
def gapB : Matrix (Fin 2) (Fin 2) ℝ := !![-1, -1; 1, 0]

/-- Interface of the example: the first coordinate. -/
def gapU : Fin 1 → Fin 2 → ℝ := fun _ i => if i = 0 then 1 else 0

/-- Channel map of the example (one piece, one channel). -/
def gapCh : Fin 1 → Fin 1 := fun _ => 0

/-- Load of the example. -/
def gapR : Fin 1 → ℝ := fun _ => 1

theorem gap_pencil_det (q : Fin 2 → ℝ) (ℓ : Fin 1 → ℂ) (z : ℂ) :
    (pencil gapB gapU gapU q ℓ z).det = (z * q 0 + 1 - ℓ 0) * (z * q 1) + 1 := by
  rw [Matrix.det_fin_two]
  simp [pencil, gapB, gapU]

/-- The reduced determinant of the example has no zero in the closed right half-plane. -/
theorem gap_det_ne {z : ℂ} (hre : 0 ≤ z.re) {q0 q1 t : ℝ} (hq0 : 0 < q0) (hq1 : 0 < q1)
    (ht : 0 < t) : (z * q0 + 1 - 1 / (1 + z * t)) * (z * q1) + 1 ≠ 0 := by
  intro h
  by_cases hz : z = 0
  · rw [hz] at h; simp at h
  have hq1c : (q1 : ℂ) ≠ 0 := by exact_mod_cast hq1.ne'
  have hzq : z * (q1 : ℂ) ≠ 0 := mul_ne_zero hz hq1c
  set E0 := z * q0 + 1 - 1 / (1 + z * t) with hE0
  have hE : E0 = -(z * q1)⁻¹ := by
    rw [eq_neg_iff_add_eq_zero, ← mul_right_inj' hzq]
    rw [mul_add, mul_inv_cancel₀ hzq]
    linear_combination h
  have hns : 0 < Complex.normSq (z * q1) := Complex.normSq_pos.mpr hzq
  have hinv : 0 ≤ ((z * q1)⁻¹).re := by
    rw [Complex.inv_re]
    apply div_nonneg _ hns.le
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg hre hq1.le
  have hEre : E0.re ≤ 0 := by rw [hE]; simp only [Complex.neg_re]; linarith
  -- the real part of the lag factor is below one away from `z = 0`
  have hden : (1 + z * (t : ℂ)) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; nlinarith [mul_nonneg hre ht.le]
  have hlag : (1 / (1 + z * (t : ℂ))).re < 1 := by
    rw [one_div, Complex.inv_re]
    have hn : 0 < Complex.normSq (1 + z * (t : ℂ)) := Complex.normSq_pos.mpr hden
    rw [div_lt_one hn]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, add_zero, zero_add]
    have hzne : z.re ≠ 0 ∨ z.im ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hz (Complex.ext (by simp [hc.1]) (by simp [hc.2]))
    rcases hzne with ha | hb
    · have ha' : 0 < z.re := lt_of_le_of_ne hre (Ne.symm ha)
      nlinarith [mul_pos ha' ht, sq_nonneg (z.im * t), mul_pos (mul_pos ha' ht) (mul_pos ha' ht)]
    · have hb2 : 0 < (z.im * t) ^ 2 := by positivity
      nlinarith [mul_nonneg hre ht.le, mul_nonneg (mul_nonneg hre ht.le) (mul_nonneg hre ht.le)]
  have hE0re : E0.re = z.re * q0 + 1 - (1 / (1 + z * (t : ℂ))).re := by
    simp [hE0, Complex.mul_re]
  nlinarith [mul_nonneg hre hq0.le]

/-- **The example star is D-stable.** -/
theorem gap_star_dStable : DStable (star gapB gapU gapU gapCh gapR) := by
  intro d hd z y hy
  by_contra hnot
  have hre : 0 ≤ z.re := not_lt.mp hnot
  have ht : ∀ p : Fin 1, 0 < (d (.inr p))⁻¹ := fun p => inv_pos.mpr (hd _)
  have hz1 : ∀ p : Fin 1, 1 + z * ((d (.inr p))⁻¹ : ℝ) ≠ 0 :=
    fun p => one_add_mul_ne hre (ht p).le
  obtain ⟨x, hx, hker⟩ := pencil_kernel_of_eigenpair gapB gapU gapU gapCh gapR d hd z y hy hz1
  have hdet := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩
  rw [gap_pencil_det] at hdet
  have hℓ : lagValue gapCh gapR (fun p => (d (.inr p))⁻¹) z 0 =
      1 / (1 + z * (((d (.inr 0))⁻¹ : ℝ) : ℂ)) := by
    simp [lagValue, gapCh, gapR]
  rw [hℓ] at hdet
  exact gap_det_ne hre (inv_pos.mpr (hd (.inl 0))) (inv_pos.mpr (hd (.inl 1))) (ht 0) hdet

/-- **Its all-static boundary system has the eigenvalue `i` at unit scaling.** -/
theorem gap_static_eigenpair : ∃ y, HasEigenpair
    (rightScale (bdSystem gapB gapU gapU gapCh gapR (fun _ => Role.F)) (fun _ => 1)) I y := by
  have hker : pencil (bdCore gapB gapU gapU gapCh gapR (fun _ => Role.F)) gapU gapU
      (fun _ => 1) (lagValue id (bdLoad gapCh gapR (fun _ => Role.F)) (fun _ => 1) I) I *ᵥ
        ![1, -I] = 0 := by
    have hL : ∀ c, lagValue id (bdLoad gapCh gapR (fun _ => Role.F)) (fun _ => 1) I c = 0 := by
      intro c; simp [lagValue, bdLoad]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, pencil, bdCore, gapB, gapU, gapCh, gapR, hL,
        Fin.sum_univ_two]
  have hx : (![1, -I] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨y, hy⟩ := eigenpair_of_pencil_kernel
    (bdCore gapB gapU gapU gapCh gapR (fun _ => Role.F)) gapU gapU id
    (bdLoad gapCh gapR (fun _ => Role.F)) (fun _ => 1) (fun _ => 1) (fun _ => one_pos)
    (fun _ => one_pos) I (fun _ => one_add_mul_ne (by simp) zero_le_one) _ hx hker
  have hsc : (Sum.elim (fun _ : Fin 2 => ((1 : ℝ))⁻¹) (fun _ : Fin 1 => ((1 : ℝ))⁻¹) :
      Fin 2 ⊕ Fin 1 → ℝ) = fun _ => 1 := by
    funext a; rcases a with i | c <;> simp
  rw [hsc] at hy
  exact ⟨y, hy⟩

/-- **Its all-static boundary system is not D-stable.** -/
theorem gap_static_not_dStable :
    ¬ DStable (bdSystem gapB gapU gapU gapCh gapR (fun _ => Role.F)) := by
  intro hst
  obtain ⟨y, hy⟩ := gap_static_eigenpair
  have := hst _ (fun _ => one_pos) I y hy
  simp at this

/-- **Marginal gap.** A D-stable star with nonzero loads may have a boundary system that is not
D-stable. -/
theorem marginal_gap : (∀ p, gapR p ≠ 0) ∧ DStable (star gapB gapU gapU gapCh gapR) ∧
    (∃ y, HasEigenpair
      (rightScale (bdSystem gapB gapU gapU gapCh gapR (fun _ => Role.F)) (fun _ => 1)) I y) ∧
    ¬ DStable (bdSystem gapB gapU gapU gapCh gapR (fun _ => Role.F)) :=
  ⟨fun _ => one_ne_zero, gap_star_dStable, gap_static_eigenpair, gap_static_not_dStable⟩

end DStabilityLocalization
