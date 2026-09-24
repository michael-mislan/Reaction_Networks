import proofs.ProductiveRecovery.PhaseComparison
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ProductiveRecovery
noncomputable section
open Set

theorem factor_comparison (f v g w : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (v t) t)
    (hg : ∀ t, HasDerivAt g (w t) t) (h0 : g 0 ≤ f 0)
    (hv : ∀ t, 0 ≤ t → w t ≤ Real.exp (70*t)*(v t+70*f t)) :
    ∀ t, 0 ≤ t → g t ≤ Real.exp (70*t)*f t := by
  have hE (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun s => Real.exp (70*s)*f s)
        (Real.exp (70*t)*(v t+70*f t)) t := by
    convert ((((hasDerivAt_id t).const_mul 70).exp).mul (hf t ht)) using 1
    simp only [id_eq]
    ring
  intro t ht
  exact image_le_of_deriv_right_le_deriv_boundary
    (fun s _ => (hg s).continuousAt.continuousWithinAt)
    (fun s _ => (hg s).hasDerivWithinAt)
    (by simpa using h0)
    (fun s hs => (hE s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hE s hs.1).hasDerivWithinAt)
    (fun s hs => hv s hs.1) ⟨ht,le_rfl⟩

theorem phase_transfer (X V : ℝ → State)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (V t) t)
    (hp : ∀ t, 0 ≤ t →
      -70*X t 2+20*X t 3+38*X t 5 ≤ V t 2 ∧
      -70*X t 3+20*X t 4 ≤ V t 3 ∧
      -70*X t 4 ≤ V t 4 ∧ -70*X t 5+20*X t 4 ≤ V t 5) :
    ∀ h, 0 ≤ h →
      X 0 2+20*h*X 0 3+580*h^2*X 0 4+38*h*X 0 5 ≤
        Real.exp (70*h)*X h 2 := by
  have hd (i : Fin 6) (t : ℝ) (ht : 0 ≤ t) := hasDerivAt_pi.1 (hX t ht) i
  have hc2 := factor_comparison (fun t => X t 4) (fun t => V t 4)
    (fun _ => X 0 4) (fun _ => 0) (hd 4) (fun t => hasDerivAt_const t _) le_rfl
    (fun t ht => mul_nonneg (Real.exp_pos _).le (by linarith [(hp t ht).2.2.1]))
  have hc1 := factor_comparison (fun t => X t 3) (fun t => V t 3)
    (fun t => X 0 3+20*t*X 0 4) (fun _ => 20*X 0 4) (hd 3)
    (fun t => by convert (((hasDerivAt_id t).const_mul 20).mul_const (X 0 4)).const_add (X 0 3) using 1; ring)
    (by simp) (fun t ht => by
      have hh := mul_le_mul_of_nonneg_left (hp t ht).2.1 (Real.exp_pos (70*t)).le
      nlinarith [hc2 t ht])
  have hz := factor_comparison (fun t => X t 5) (fun t => V t 5)
    (fun t => X 0 5+20*t*X 0 4) (fun _ => 20*X 0 4) (hd 5)
    (fun t => by convert (((hasDerivAt_id t).const_mul 20).mul_const (X 0 4)).const_add (X 0 5) using 1; ring)
    (by simp) (fun t ht => by
      have hh := mul_le_mul_of_nonneg_left (hp t ht).2.2.2 (Real.exp_pos (70*t)).le
      nlinarith [hc2 t ht])
  apply factor_comparison (fun t => X t 2) (fun t => V t 2)
    (fun t => X 0 2+20*t*X 0 3+580*t^2*X 0 4+38*t*X 0 5)
    (fun t => 20*X 0 3+1160*t*X 0 4+38*X 0 5) (hd 2)
  · intro t
    convert (((((hasDerivAt_id t).const_mul 20).mul_const (X 0 3)).const_add (X 0 2)).add
      ((((hasDerivAt_id t).pow 2).const_mul 580).mul_const (X 0 4))).add
      (((hasDerivAt_id t).const_mul 38).mul_const (X 0 5)) using 1
    simp only [id_eq]
    ring
  · simp
  · intro t ht
    have hh := mul_le_mul_of_nonneg_left (hp t ht).1 (Real.exp_pos (70*t)).le
    nlinarith [hc1 t ht,hz t ht]

end
end ProductiveRecovery

