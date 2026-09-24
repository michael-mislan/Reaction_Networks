import proofs.RAF1519.Refinement.IntermediateBounds
import Mathlib

namespace RAF1519.Refinement
noncomputable section
open Set

def envelope (t : ℝ) : ℝ := 9/1000+(201/100000)*Real.exp (-3*t)

theorem envelope_deriv (t : ℝ) :
    HasDerivAt envelope (-3*(envelope t-9/1000)) t := by
  convert ((((hasDerivAt_id t).const_mul (-3)).exp).const_mul (201/100000)).const_add (9/1000) using 1
  dsimp [envelope]
  ring

/-- Scalar comparison on an actual differentiable intermediate path. No assumed return. -/
theorem intermediate_comparison (b v h : ℝ → ℝ) (d T : ℝ)
    (hd : 1/50 ≤ d) (hd' : d ≤ 1/25) (hT : 0 ≤ T)
    (hb0 : b 0 ≤ 1101/100000)
    (hb : ∀ t ∈ Icc 0 T, HasDerivAt b (v t) t)
    (hh : ∀ t ∈ Icc 0 T, h t ≤ 8800000121/8000000000)
    (hv : ∀ t ∈ Icc 0 T, v t = d*(1+1/100)*h t-
      (1+d*(1+1/100)/(1/100))*b t) :
    b T ≤ envelope T := by
  have hk := kappa_bounds d hd hd'
  have hg := forcing_gap d hd'
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f := b) (f' := v) (a := 0) (b := T)
    (fun t ht => (hb t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hb t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (B := envelope) (B' := fun t => -3*(envelope t-9/1000))
    (by norm_num [envelope]; exact hb0) envelope_deriv
    (fun t ht heq => ?_) ⟨hT,le_rfl⟩
  have hm := mul_le_mul_of_nonneg_left (hh t ⟨ht.1,ht.2.le⟩)
    (show 0 ≤ d*(1+1/100) by linarith)
  have hp : 0 ≤ envelope t-9/1000 := by
    dsimp [envelope]
    linarith [Real.exp_pos (-3*t)]
  have hprod := mul_nonneg (show 0 ≤ 1+d*(1+1/100)/(1/100)-3 by linarith [hk.1]) hp
  rw [hv t ⟨ht.1,ht.2.le⟩,heq]
  nlinarith

theorem envelope_endpoint : envelope 4 < 904/100000 := by
  have h4 := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4) 8
  norm_num [Finset.sum_range_succ] at h4
  have he4 : (50:ℝ) < Real.exp 4 := by linarith
  have he12 : (125000:ℝ) < Real.exp 12 := by
    have he : Real.exp 12 = Real.exp 4 * Real.exp 4 * Real.exp 4 := by
      rw [← Real.exp_add,← Real.exp_add]; norm_num
    rw [he]
    nlinarith [sq_nonneg (Real.exp 4-50)]
  have hneg : Real.exp (-12) < (1/125000:ℝ) := by
    rw [Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos 12) (by norm_num)).2
    norm_num
    exact he12
  dsimp [envelope]
  norm_num at hneg ⊢
  linarith
end
end RAF1519.Refinement
