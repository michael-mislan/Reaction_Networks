import proofs.CompositionalMemory.GenericLocalMoments
import proofs.CompositionalMemory.GenericJumpBound

namespace CompositionalMemory

theorem norm_bilinear_jump_small {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y jump : V) (α v L r D : ℝ) (hv : 0 < v) (hα : 0 ≤ α)
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hop : ∀ x q, |Q x q| ≤ L*‖x‖*‖q‖)
    (hy : ‖y‖ ≤ r) (hj : ‖jump‖ ≤ D/v)
    (hsmall : α*(2*L*r*D+L*D^2/v) ≤ 1) :
    |α*v*(Q (y+jump) (y+jump)-Q y y)| ≤ 1 := by
  have hn : ‖v • jump‖ ≤ D := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hv]
    calc
      _ ≤ v*(D/v) := mul_le_mul_of_nonneg_left hj hv.le
      _ = D := by field_simp
  have hD : 0 ≤ D := (norm_nonneg _).trans hn
  have hu : |Q y (v • jump)| ≤ L*r*D := (hop _ _).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hy hL) hn (norm_nonneg _) (mul_nonneg hL hr))
  have hq : |Q (v • jump) (v • jump)| ≤ L*D^2 := by
    have h := (hop _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hn hL) hn
      (norm_nonneg _) (mul_nonneg hL hD))
    convert h using 1
    ring
  have hs := bilinear_scaled_jump_small Q hQ y (v • jump) α v (L*r*D) (L*D^2)
    hv hα hu hq (by convert hsmall using 1; ring)
  have hvone : (1/v)*v=1 := by field_simp
  simpa only [smul_smul,hvone,one_smul] using hs

theorem generic_local_jump_small {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y u b : V) (ν : ι → V) (α v L r U P R : ℝ)
    (hv : 0 < v) (hα : 0 ≤ α) (hL : 0 ≤ L) (hr : 0 ≤ r) (hU : 0 ≤ U)
    (hop : ∀ x q, |Q x q| ≤ L*‖x‖*‖q‖)
    (hy : ‖y‖ ≤ r) (hu : ‖u‖ ≤ U) (hb : ‖b‖ ≤ 1)
    (hcross : ∀ j, |Q y (ν j)| ≤ P*r) (hquad : ∀ j, |Q (ν j) (ν j)| ≤ R)
    (hsres : α*(2*(P*r)+R/v) ≤ 1)
    (hscouple : α*(2*L*r*(U+1)+L*(U+1)^2/v) ≤ 1) :
    ∀ j, |α*v*(Q (y+localChannelJump ν u b v i j) (y+localChannelJump ν u b v i j)-Q y y)| ≤ 1 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hunit (q : V) (hq : ‖q‖ ≤ 1) : ‖(1/v) • q‖ ≤ (U+1)/v := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ (1:ℝ)/v by positivity)]
    calc
      _ ≤ (1/v)*1 := mul_le_mul_of_nonneg_left hq (by positivity)
      _ ≤ (U+1)/v := by
        simpa only [mul_one] using div_le_div_of_nonneg_right
          (show (1:ℝ) ≤ U+1 by linarith) hv.le
  intro j
  rcases j with j | j
  · exact bilinear_scaled_jump_small Q hQ y (ν j) α v (P*r) R hv hα (hcross j) (hquad j) hsres
  · apply norm_bilinear_jump_small Q hQ y _ α v L r (U+1) hv hα hL hr hop hy _ hscouple
    rcases j with j | j
    · exact (membrane_vector_jump_norm u b (if j=i then (k:ℝ) else 0) (k*v) U
        (by split_ifs <;> positivity) (by positivity) hu hb).trans
        (membrane_jump_size hk i j (k*v) v U hv le_rfl hU)
    · rcases j with j | j
      · exact hunit (-b) (by simpa only [norm_neg] using hb)
      · exact hunit b hb

end CompositionalMemory
