import Mathlib

namespace CompositionalMemory

theorem quadratic_partition_return {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (c L r δ parent birth : ℝ) (hc : 0 < c) (hL : 0 ≤ L) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hcoerc : ∀ y, c*‖y‖^2 ≤ Q y y) (hop : ∀ x y, |Q x y| ≤ L*‖x‖*‖y‖)
    (hsize : parent ≤ c*r^2) (hbudget : parent+2*L*r*δ+L*δ^2 < birth)
    (y v : V) (hy : Q y y ≤ parent) (hv : ‖v‖ ≤ δ) : Q (y+v) (y+v) < birth := by
  have hyr : ‖y‖ ≤ r := by
    have hh := (hcoerc y).trans (hy.trans hsize)
    have hsq : ‖y‖^2 ≤ r^2 := (mul_le_mul_iff_right₀ hc).mp hh
    exact (sq_le_sq₀ (norm_nonneg y) hr).mp hsq
  have hcross : Q y v ≤ L*r*δ := (le_abs_self _).trans ((hop y v).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hyr hL) hv (norm_nonneg v) (mul_nonneg hL hr)))
  have hquad : Q v v ≤ L*δ^2 := by
    have hh := (le_abs_self _).trans (hop v v)
    have hsq : ‖v‖^2 ≤ δ^2 := (sq_le_sq₀ (norm_nonneg v) hδ).mpr hv
    have hmul := mul_le_mul_of_nonneg_left hsq hL
    nlinarith only [hh,hmul]
  have heq : Q (y+v) (y+v)=Q y y+2*Q y v+Q v v := by
    simp only [map_add,LinearMap.add_apply,hQ v y]
    ring
  rw [heq]
  linarith only [hy,hcross,hquad,hbudget]

theorem general_both_daughters_return {d : ℕ}
    (Q : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (c L r δ parent birth : ℝ) (hc : 0 < c) (hL : 0 ≤ L) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hcoerc : ∀ y, c*‖y‖^2 ≤ Q y y) (hop : ∀ x y, |Q x y| ≤ L*‖x‖*‖y‖)
    (hsize : parent ≤ c*r^2) (hbudget : parent+2*L*r*δ+L*δ^2 < birth)
    (n draw : Fin d → ℕ) (hdraw : ∀ a, draw a ≤ n a) (N : ℕ) (hN : 0 < N)
    (center : Fin d → ℝ)
    (hparent : Q (fun a => (n a:ℝ)/(2*(N:ℝ))-center a)
      (fun a => (n a:ℝ)/(2*(N:ℝ))-center a) ≤ parent)
    (hgood : ∀ a, |(draw a:ℝ)-(n a:ℝ)/2| < (N:ℝ)*δ) :
    Q (fun a => (draw a:ℝ)/(N:ℝ)-center a) (fun a => (draw a:ℝ)/(N:ℝ)-center a) < birth ∧
    Q (fun a => ((n a-draw a:ℕ):ℝ)/(N:ℝ)-center a)
      (fun a => ((n a-draw a:ℕ):ℝ)/(N:ℝ)-center a) < birth := by
  let y := fun a => (n a:ℝ)/(2*(N:ℝ))-center a
  let v := fun a => (draw a:ℝ)/(N:ℝ)-(n a:ℝ)/(2*(N:ℝ))
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hnoise (a) : v a=((draw a:ℝ)-(n a:ℝ)/2)/(N:ℝ) := by dsimp [v]; ring
  have hv : ‖v‖ ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ).mpr
    intro a
    rw [Real.norm_eq_abs,hnoise,abs_div,abs_of_pos hNr]
    apply (div_le_iff₀ hNr).mpr
    nlinarith only [(hgood a).le]
  have hfirst := quadratic_partition_return Q hQ c L r δ parent birth hc hL hr hδ
    hcoerc hop hsize hbudget y v hparent hv
  have hsecond := quadratic_partition_return Q hQ c L r δ parent birth hc hL hr hδ
    hcoerc hop hsize hbudget y (-v) hparent (by simpa only [norm_neg] using hv)
  have hfirsteq : y+v=(fun a => (draw a:ℝ)/(N:ℝ)-center a) := by
    funext a
    dsimp [y,v]
    ring
  have hsecondeq : y+(-v)=(fun a => ((n a-draw a:ℕ):ℝ)/(N:ℝ)-center a) := by
    funext a
    dsimp [y,v]
    rw [Nat.cast_sub (hdraw a)]
    ring
  exact ⟨by simpa only [hfirsteq] using hfirst,by simpa only [hsecondeq] using hsecond⟩

end CompositionalMemory
