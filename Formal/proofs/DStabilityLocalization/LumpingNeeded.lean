import proofs.DStabilityLocalization.Boundary

/-!
# Synchronization is needed

One channel (`k = 1`) with two pieces of load `125/16` on the core `[[-1,0],[1,-1]]`, read at
`x₁` and fed back negatively into `x₀` (`v = e₁`, `u = -e₀`).  The star is D-unstable (at unit
rates it has the eigenvalue `-1 + (5/2) e^{iπ/3}`), while every boundary system whose
synchronized group has at most one piece is D-stable.  So boundary systems with at most one
dynamic piece per channel do not suffice: the lumped pool of two pieces is needed.

The lower boundary systems are handled by one cubic Routh–Hurwitz inequality
(`cubic_ne_zero`): their reduced determinant, multiplied by `1 + z t`, is a cubic with positive
coefficients and `a₂a₁ - a₃a₀ ≥ (8 - R) q₀q₁t > 0`, where `R ≤ 125/16 < 8` is the lump load.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

/-- A real cubic with positive coefficients and `a₂ a₁ > a₃ a₀` has no zero with `Re z ≥ 0`. -/
theorem cubic_ne_zero {a3 a2 a1 a0 : ℝ} (h3 : 0 < a3) (h2 : 0 < a2) (h1 : 0 < a1)
    (h0 : 0 < a0) (hH : a3 * a0 < a2 * a1) {z : ℂ} (hre : 0 ≤ z.re) :
    (a3 : ℂ) * z ^ 3 + (a2 : ℂ) * z ^ 2 + (a1 : ℂ) * z + (a0 : ℂ) ≠ 0 := by
  intro h
  have hR := congrArg Complex.re h
  have hI := congrArg Complex.im h
  simp only [pow_succ, pow_zero, one_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im,
    zero_mul, sub_zero, add_zero, mul_zero, zero_add] at hR hI
  set x := z.re
  set y := z.im
  by_cases hy : y = 0
  · rw [hy] at hR
    have : 0 < a3 * (x * x * x) + a2 * (x * x) + a1 * x + a0 := by positivity
    nlinarith
  · -- the imaginary part gives `a₃ y² = 3a₃x² + 2a₂x + a₁`
    have hI' : a3 * y ^ 2 = 3 * a3 * x ^ 2 + 2 * a2 * x + a1 := by
      have : y * (a3 * (3 * x ^ 2 - y ^ 2) + 2 * a2 * x + a1) = 0 := by
        linear_combination hI
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hy
      · linear_combination -h'
    have key : a3 * (a3 * (x * x * x) - 3 * a3 * x * y ^ 2 + a2 * (x * x) - a2 * y ^ 2 +
        a1 * x + a0) + (3 * a3 * x + a2) * (a3 * y ^ 2 - (3 * a3 * x ^ 2 + 2 * a2 * x + a1)) =
        -8 * a3 ^ 2 * x ^ 3 - 8 * a2 * a3 * x ^ 2 - 2 * a1 * a3 * x - 2 * a2 ^ 2 * x +
          (a0 * a3 - a1 * a2) := by ring
    have hRe : a3 * (x * x * x) - 3 * a3 * x * y ^ 2 + a2 * (x * x) - a2 * y ^ 2 + a1 * x + a0
        = 0 := by linear_combination hR
    rw [hRe, hI'] at key
    have hx3 : 0 ≤ x ^ 3 := pow_nonneg hre 3
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg a3) hx3) (by norm_num : (0 : ℝ) ≤ 8),
      mul_nonneg (mul_nonneg h2.le h3.le) hx2, mul_nonneg (mul_nonneg h1.le h3.le) hre,
      mul_nonneg (sq_nonneg a2) hre]

/-- Core of the example. -/
def lumpB : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 1, -1]

/-- Feedback direction `-e₀`. -/
def lumpU : Fin 1 → Fin 2 → ℝ := fun _ i => if i = 0 then -1 else 0

/-- Read-out `e₁`. -/
def lumpV : Fin 1 → Fin 2 → ℝ := fun _ i => if i = 1 then 1 else 0

/-- Both pieces belong to the single channel. -/
def lumpCh : Fin 2 → Fin 1 := fun _ => 0

/-- Loads `125/16` (total loop gain `125/8 ∈ (8, 16)`). -/
def lumpR : Fin 2 → ℝ := fun _ => 125 / 16

/-- The static load of a boundary choice. -/
def lumpX (σ : Fin 2 → Role) : ℝ := ∑ p, if σ p = Role.F then lumpR p else 0

theorem lump_pencil_det (σ : Fin 2 → Role) (q : Fin 2 → ℝ) (ℓ : Fin 1 → ℂ) (z : ℂ) :
    (pencil (bdCore lumpB lumpU lumpV lumpCh lumpR σ) lumpU lumpV q ℓ z).det =
      (z * q 0 + 1) * (z * q 1 + 1) + (lumpX σ : ℂ) + ℓ 0 := by
  rw [Matrix.det_fin_two]
  unfold lumpX
  by_cases h0 : σ 0 = Role.F <;> by_cases h1 : σ 1 = Role.F <;>
    simp [pencil, bdCore, lumpB, lumpU, lumpV, lumpCh, lumpR, Fin.sum_univ_two, h0, h1] <;>
    ring

/-- **Every boundary system with at most one synchronized piece is D-stable.** -/
theorem lump_lower_dStable (σ : Fin 2 → Role) (hσ : ¬ (σ 0 = Role.D ∧ σ 1 = Role.D)) :
    DStable (bdSystem lumpB lumpU lumpV lumpCh lumpR σ) := by
  intro d hd z y hy
  by_contra hnot
  have hre : 0 ≤ z.re := not_lt.mp hnot
  have ht : ∀ c : Fin 1, 0 < (d (.inr c))⁻¹ := fun c => inv_pos.mpr (hd _)
  obtain ⟨x, hx, hker⟩ := pencil_kernel_of_eigenpair (bdCore lumpB lumpU lumpV lumpCh lumpR σ)
    lumpU lumpV id (bdLoad lumpCh lumpR σ) d hd z y hy (fun c => one_add_mul_ne hre (ht c).le)
  have hdet := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hker⟩
  rw [lump_pencil_det] at hdet
  set q0 := (d (.inl 0))⁻¹
  set q1 := (d (.inl 1))⁻¹
  set t := (d (.inr 0))⁻¹
  set R := bdLoad lumpCh lumpR σ 0
  set X := lumpX σ
  have hq0 : 0 < q0 := inv_pos.mpr (hd _)
  have hq1 : 0 < q1 := inv_pos.mpr (hd _)
  have htp : 0 < t := ht 0
  have hL : lagValue id (bdLoad lumpCh lumpR σ) (fun c => (d (.inr c))⁻¹) z 0 =
      (R : ℂ) / (1 + z * (t : ℂ)) := by
    show (∑ p : Fin 1, if p = 0 then (bdLoad lumpCh lumpR σ p : ℂ) /
      (1 + z * (((d (.inr p))⁻¹ : ℝ) : ℂ)) else 0) = _
    rw [Fintype.sum_eq_single 0 (fun c hc => if_neg hc), if_pos rfl]
  rw [hL] at hdet
  -- bounds on the loads
  have hX : 0 ≤ X := by
    unfold X lumpX
    exact Finset.sum_nonneg (fun p _ => by split_ifs <;> norm_num [lumpR])
  have hR0 : 0 ≤ R := by
    unfold R bdLoad
    exact Finset.sum_nonneg (fun p _ => by split_ifs <;> norm_num [lumpR])
  have hR8 : R < 8 := by
    have e : R = (if σ 0 = Role.D then 125 / 16 else 0) + (if σ 1 = Role.D then 125 / 16 else 0) := by
      simp [R, bdLoad, lumpCh, lumpR, Fin.sum_univ_two]
    rw [e]
    by_cases h0 : σ 0 = Role.D <;> by_cases h1 : σ 1 = Role.D
    · exact absurd ⟨h0, h1⟩ hσ
    all_goals norm_num [h0, h1]
  -- clear the lag and apply the cubic criterion
  have hden : (1 : ℂ) + z * (t : ℂ) ≠ 0 := one_add_mul_ne hre htp.le
  have hcubic : ((q0 * q1 * t : ℝ) : ℂ) * z ^ 3 + ((q0 * q1 + q0 * t + q1 * t : ℝ) : ℂ) * z ^ 2 +
      ((q0 + q1 + t + X * t : ℝ) : ℂ) * z + ((1 + X + R : ℝ) : ℂ) = 0 := by
    have := congrArg (fun w => w * (1 + z * (t : ℂ))) hdet
    simp only [zero_mul] at this
    field_simp at this
    push_cast
    linear_combination this
  refine cubic_ne_zero (by positivity) (by positivity) (by positivity) (by positivity) ?_ hre
    hcubic
  -- `a₂ a₁ - a₃ a₀ ≥ (8 - R) q₀q₁t + X t² (q₀ + q₁) > 0`
  have sos : (q0 * q1 + q0 * t + q1 * t) * (q0 + q1 + t) - 9 * (q0 * q1 * t) =
      q0 * (q1 - t) ^ 2 + q1 * (q0 - t) ^ 2 + t * (q0 - q1) ^ 2 := by ring
  have hsos : 0 ≤ q0 * (q1 - t) ^ 2 + q1 * (q0 - t) ^ 2 + t * (q0 - q1) ^ 2 := by positivity
  have hp : 0 < q0 * q1 * t := by positivity
  nlinarith [mul_pos hp (by linarith : (0 : ℝ) < 8 - R),
    mul_nonneg hX (mul_nonneg (sq_nonneg t) (add_pos hq0 hq1).le)]

/-- `μ = 5/4 + (5√3/4) i`, so that `μ³ = -125/8`. -/
def lumpMu : ℂ := (5 / 4 : ℂ) + ((5 * Real.sqrt 3 / 4 : ℝ) : ℂ) * I

theorem lumpMu_cube : lumpMu ^ 3 = -(125 / 8 : ℂ) := by
  set a : ℝ := 5 * Real.sqrt 3 / 4 with ha_def
  have ha : a ^ 2 = 75 / 16 := by
    rw [ha_def, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have ha' : (a : ℂ) ^ 2 = 75 / 16 := by
    have := congrArg (fun w : ℝ => (w : ℂ)) ha
    push_cast at this
    exact this
  have hI : I ^ 2 = -1 := Complex.I_sq
  show ((5 / 4 : ℂ) + (a : ℂ) * I) ^ 3 = -(125 / 8 : ℂ)
  linear_combination (-15 / 4 - (a : ℂ) * I) * ha' + (15 / 4 * (a : ℂ) ^ 2 + (a : ℂ) ^ 3 * I) * hI

/-- **The star is D-unstable**: at unit rates it has the eigenvalue `μ - 1`, `Re = 1/4`. -/
theorem lump_star_eigenpair : ∃ y, HasEigenpair (rightScale (star lumpB lumpU lumpV lumpCh lumpR)
    (fun _ => 1)) (lumpMu - 1) y := by
  set μ := lumpMu
  refine ⟨Sum.elim (fun i : Fin 2 => if i = 0 then μ ^ 2 else μ) (fun _ => 1), ?_, ?_⟩
  · intro h0
    have := congrFun h0 (.inr 0)
    simp at this
  · intro a
    have hc := lumpMu_cube
    rcases a with i | p
    · rw [star_mulVec_inl]
      fin_cases i
      · simp [lumpB, lumpU, lumpV, lumpCh, lumpR, Fin.sum_univ_two]
        linear_combination (-1 : ℂ) * hc
      · simp [lumpB, lumpU, lumpV, lumpCh, lumpR, Fin.sum_univ_two]
        ring
    · rw [star_mulVec_inr]
      simp [lumpB, lumpU, lumpV, lumpCh, lumpR, Fin.sum_univ_two]

theorem lump_star_dUnstable : DUnstable (star lumpB lumpU lumpV lumpCh lumpR) := by
  obtain ⟨y, hy⟩ := lump_star_eigenpair
  refine ⟨fun _ => 1, fun _ => one_pos, lumpMu - 1, y, ?_, hy⟩
  simp [lumpMu]
  norm_num

/-- **Synchronization is needed.** The loads are nonzero, the star is D-unstable, and every
boundary system whose synchronized group has at most one piece is D-stable. -/
theorem lumping_needed : (∀ p, lumpR p ≠ 0) ∧ DUnstable (star lumpB lumpU lumpV lumpCh lumpR) ∧
    ∀ σ : Fin 2 → Role, ¬ (σ 0 = Role.D ∧ σ 1 = Role.D) →
      DStable (bdSystem lumpB lumpU lumpV lumpCh lumpR σ) :=
  ⟨fun _ => by norm_num [lumpR], lump_star_dUnstable, lump_lower_dStable⟩

end DStabilityLocalization
