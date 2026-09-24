import proofs.CompositionalMemory.FiniteIntegerRows

namespace CompositionalMemory.FiniteIntegerRows
set_option maxHeartbeats 40000
attribute [local irreducible] CompositionalMemory.FiniteIntegerRows.residual
  CompositionalMemory.FiniteIntegerRows.shiftedResidual
  CompositionalMemory.FiniteIntegerRows.growthDifference

theorem cast_abs_bound (z : Int) (B : Nat) (h : z.natAbs ≤ B) :
    |(z : ℝ)| ≤ (B : ℝ) := by
  have he : |(z : ℝ)|=(z.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [he]
  exact_mod_cast h

theorem perturbed_fraction_bound (r g R G D S δ ρ ε : ℝ)
    (hD : 0 < D) (hS : 0 < S) (hρ : 0 ≤ ρ)
    (hr : |r| ≤ R) (hg : |g| ≤ G) (hδ : |δ| ≤ ρ)
    (hb : R/D+ρ*G/S ≤ ε) : |r/D+δ*g/S| ≤ ε := by
  calc
    _ ≤ |r/D|+|δ*g/S| := abs_add_le _ _
    _ = |r|/D+|δ| * |g|/S := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hD,abs_of_pos hS]
    _ ≤ R/D+ρ*G/S := by
      apply add_le_add (div_le_div_of_nonneg_right hr hD.le)
      exact div_le_div_of_nonneg_right
        (mul_le_mul hδ hg (abs_nonneg g) hρ) hS.le
    _ ≤ ε := hb

noncomputable def realResidual (m : Nat) (v next : Array Int) (i col : Nat) (γ : ℝ) : ℝ :=
  (residual m v next i col : ℝ)/(10*(m : ℝ)*(scale : ℝ))+
    (γ-1/10)*(growthDifference m v next i col : ℝ)/(scale : ℝ)

noncomputable def realShiftedResidual (m : Nat) (v next : Array Int) (i col : Nat) (γ : ℝ) : ℝ :=
  (shiftedResidual m v next i col : ℝ)/(40*(m : ℝ)*(scale : ℝ))+
    (γ-1/10)*(growthDifference m v next i col : ℝ)/(scale : ℝ)

theorem limits_value_real (m : Nat) (hm : 0 < m) (lim : Limits)
    (h : limitsOK m lim=true) :
    (lim.residual : ℝ)/(10*(m : ℝ)*(scale : ℝ))+
      (1/10000000 : ℝ)*(lim.valueSensitivity : ℝ)/(scale : ℝ) ≤ 1/10000 := by
  have hb := (of_decide_eq_true h).1
  have hb' : (1000000 : ℝ)*lim.residual+(m : ℝ)*lim.valueSensitivity ≤
      1000*(m : ℝ)*(scale : ℝ) := by
    norm_num [scale] at hb ⊢
    exact_mod_cast hb
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (lim.residual : ℝ)/(10*(m : ℝ)*(scale : ℝ))+
      (1/10000000 : ℝ)*(lim.valueSensitivity : ℝ)/(scale : ℝ) =
      (1000000*(lim.residual : ℝ)+(m : ℝ)*lim.valueSensitivity)/
        (10000000*(m : ℝ)*(scale : ℝ)) := by
    norm_num [scale]
    field_simp; ring
  rw [he]
  apply (div_le_iff₀ (by norm_num [scale]; positivity)).mpr
  nlinarith only [hb']

theorem limits_mgf_real (m : Nat) (hm : 0 < m) (lim : Limits)
    (h : limitsOK m lim=true) :
    (lim.mgfResidual : ℝ)/(40*(m : ℝ)*(scale : ℝ))+
      (1/10000000 : ℝ)*(lim.mgfSensitivity : ℝ)/(scale : ℝ) ≤ 1/4000 := by
  have hb := (of_decide_eq_true h).2
  have hb' : (250000 : ℝ)*lim.mgfResidual+(m : ℝ)*lim.mgfSensitivity ≤
      2500*(m : ℝ)*(scale : ℝ) := by
    norm_num [scale] at hb ⊢
    exact_mod_cast hb
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (lim.mgfResidual : ℝ)/(40*(m : ℝ)*(scale : ℝ))+
      (1/10000000 : ℝ)*(lim.mgfSensitivity : ℝ)/(scale : ℝ) =
      (250000*(lim.mgfResidual : ℝ)+(m : ℝ)*lim.mgfSensitivity)/
        (10000000*(m : ℝ)*(scale : ℝ)) := by
    norm_num [scale]
    field_simp; ring
  rw [he]
  apply (div_le_iff₀ (by norm_num [scale]; positivity)).mpr
  nlinarith only [hb']

theorem checked_real_rows (m : Nat) (hm : 0 < m) (v next : Array Int) (lim : Limits)
    (hlim : limitsOK m lim=true) (i : Nat) (hrow : rowOK m v next lim i=true)
    (γ : ℝ) (hγ : |γ-1/10| ≤ 1/10000000) :
    |realResidual m v next i 0 γ| ≤ 1/10000 ∧
    |realResidual m v next i 1 γ| ≤ 1/10000 ∧
    |realShiftedResidual m v next i 2 γ| ≤ 1/4000 := by
  have h := of_decide_eq_true hrow
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hS : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]
  have hD : (0 : ℝ) < 10*(m : ℝ)*(scale : ℝ) := by positivity
  have hE : (0 : ℝ) < 40*(m : ℝ)*(scale : ℝ) := by positivity
  refine ⟨?_,?_,?_⟩
  · exact perturbed_fraction_bound _ _ _ _ _ _ _ _ _ hD hS (by norm_num)
      (cast_abs_bound _ _ h.1) (cast_abs_bound _ _ h.2.2.2.1) hγ
      (limits_value_real m hm lim hlim)
  · exact perturbed_fraction_bound _ _ _ _ _ _ _ _ _ hD hS (by norm_num)
      (cast_abs_bound _ _ h.2.1) (cast_abs_bound _ _ h.2.2.2.2.1) hγ
      (limits_value_real m hm lim hlim)
  · exact perturbed_fraction_bound _ _ _ _ _ _ _ _ _ hE hS (by norm_num)
      (cast_abs_bound _ _ h.2.2.1) (cast_abs_bound _ _ h.2.2.2.2.2.1) hγ
      (limits_mgf_real m hm lim hlim)

end CompositionalMemory.FiniteIntegerRows
