import proofs.CoreCouplingGlobal.ScalarComparison

open Filter Topology

namespace RobustPermanence

/-- A positive scalar trajectory satisfying logistic lower drift has an eventual
floor. This is a physical-time statement, not a frozen equilibrium test. -/
theorem eventual_lower_of_logistic_drift
    (y v : ℝ → ℝ) (T gamma beta : ℝ)
    (hg : 0 < gamma) (hb : 0 < beta)
    (hy : ∀ t, T ≤ t → 0 < y t)
    (hd : ∀ t, T ≤ t → HasDerivAt y (v t) t)
    (hv : ∀ t, T ≤ t → y t * (gamma - beta * y t) ≤ v t) :
    ∀ᶠ t in atTop, gamma / (2 * beta) < y t := by
  have hrec : ∀ᶠ t in atTop, (y t)⁻¹ < 2 * beta / gamma := by
    apply CoreCouplingGlobal.eventual_upper_of_linear_drift
      (fun t => (y t)⁻¹) (fun t => -v t / (y t)^2) T beta gamma
      (2 * beta / gamma) hg
    · apply (div_lt_div_iff_of_pos_right hg).2
      linarith
    · intro t ht
      convert (hd t ht).inv (ne_of_gt (hy t ht)) using 1
    · intro t ht
      apply (div_le_iff₀ (sq_pos_of_pos (hy t ht))).2
      have hi : (y t)⁻¹ * (y t)^2 = y t := by
        field_simp
      calc
        -v t ≤ beta * (y t)^2 - gamma * y t := by nlinarith only [hv t ht]
        _ = (beta - gamma * (y t)⁻¹) * (y t)^2 := by
          rw [sub_mul, mul_assoc, hi]
  filter_upwards [hrec, eventually_ge_atTop T] with t ht htT
  have hyt := hy t htT
  have hi : (y t)⁻¹ * y t = 1 := inv_mul_cancel₀ (ne_of_gt hyt)
  have hh := (mul_lt_mul_of_pos_right ht hyt)
  rw [hi] at hh
  apply (div_lt_iff₀ (by positivity : 0 < 2 * beta)).2
  have hh' := (mul_lt_mul_of_pos_right hh hg)
  field_simp at hh'
  nlinarith only [hh']

/-- A bounded potential correction transfers a logistic floor to concentration.
The derivative inequality is the exact remaining source-level obligation. -/
theorem bounded_corrector_eventual_floor
    (x v V vV : ℝ → ℝ) (T C gamma B Vmin Vmax : ℝ)
    (hC : 0 ≤ C) (hg : 0 < gamma) (hB : 0 < B)
    (hx : ∀ t, T ≤ t → 0 < x t)
    (hV : ∀ t, T ≤ t → Vmin ≤ V t ∧ V t ≤ Vmax)
    (dx : ∀ t, T ≤ t → HasDerivAt x (v t) t)
    (dV : ∀ t, T ≤ t → HasDerivAt V (vV t) t)
    (hgrowth : ∀ t, T ≤ t →
      x t * (gamma - B * x t) ≤ v t - C * x t * vV t) :
    ∀ᶠ t in atTop,
      gamma / (2 * (B * Real.exp (C * Vmax))) * Real.exp (C * Vmin) < x t := by
  let y := fun t => x t * Real.exp (-C * V t)
  let vy := fun t => (v t - C * x t * vV t) * Real.exp (-C * V t)
  have he (t : ℝ) : 0 < Real.exp (-C * V t) := Real.exp_pos _
  have hcancel (t : ℝ) : y t * Real.exp (C * V t) = x t := by
    dsimp [y]
    rw [mul_assoc, ← Real.exp_add]
    simp
  have hy : ∀ t, T ≤ t → 0 < y t := fun t ht => mul_pos (hx t ht) (he t)
  have hdy : ∀ t, T ≤ t → HasDerivAt y (vy t) t := by
    intro t ht
    convert (dx t ht).mul (((dV t ht).const_mul (-C)).exp) using 1
    dsimp [y, vy]
    ring
  have hlog : ∀ t, T ≤ t →
      y t * (gamma - (B * Real.exp (C * Vmax)) * y t) ≤ vy t := by
    intro t ht
    have hupper : x t ≤ y t * Real.exp (C * Vmax) := by
      rw [← hcancel t]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hV t ht).2 hC))
        (le_of_lt (hy t ht))
    have hmul := mul_le_mul_of_nonneg_left hupper (le_of_lt hB)
    have hgrowth' := mul_le_mul_of_nonneg_right (hgrowth t ht) (le_of_lt (he t))
    have hcompare := mul_le_mul_of_nonneg_left hmul (le_of_lt (hy t ht))
    dsimp [vy]
    calc
      y t * (gamma - (B * Real.exp (C * Vmax)) * y t)
          ≤ y t * (gamma - B * x t) := by nlinarith only [hcompare]
      _ ≤ (v t - C * x t * vV t) * Real.exp (-C * V t) := by
        simpa only [y, mul_assoc, mul_left_comm, mul_comm] using hgrowth'
  have hl := eventual_lower_of_logistic_drift y vy T gamma
    (B * Real.exp (C * Vmax)) hg (mul_pos hB (Real.exp_pos _)) hy hdy hlog
  filter_upwards [hl, eventually_ge_atTop T] with t ht htT
  have hlow : Real.exp (C * Vmin) ≤ Real.exp (C * V t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hV t htT).1 hC)
  calc
    _ < y t * Real.exp (C * Vmin) :=
      mul_lt_mul_of_pos_right ht (Real.exp_pos _)
    _ ≤ y t * Real.exp (C * V t) :=
      mul_le_mul_of_nonneg_left hlow (le_of_lt (hy t htT))
    _ = x t := hcancel t

end RobustPermanence
