import proofs.ProductiveRecovery.SourceFlow

namespace ProductiveRecovery
noncomputable section
open Set CoreCouplingGlobal

theorem affine_material_solution (a : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt a (1-a t) t) (t : ℝ) (ht : 0 ≤ t) :
    a t = 1 + (a 0-1)*Real.exp (-t) := by
  let f := fun s => Real.exp s*(a s-1)
  have hf : ∀ s, 0 ≤ s → HasDerivAt f 0 s := by
    intro s hs
    convert (Real.hasDerivAt_exp s).mul ((hd s hs).sub_const 1) using 1
    dsimp [f]
    ring
  have heq := eq_of_has_deriv_right_eq
    (f := f) (f' := fun _ => 0) (g := fun _ => a 0-1) (a := 0) (b := t)
    (fun s hs => (hf s hs.1).hasDerivWithinAt)
    (fun s _ => (hasDerivAt_const s (a 0-1)).hasDerivWithinAt)
    (fun s hs => (hf s hs.1).continuousAt.continuousWithinAt)
    continuousOn_const (by simp [f]) t ⟨ht,le_rfl⟩
  dsimp [f] at heq
  have he : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  rw [Real.exp_neg]
  field_simp
  nlinarith

theorem scalar_material_corridor (a : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt a (1-a t) t)
    (h0 : 9/10 ≤ a 0 ∧ a 0 ≤ 11/10) :
    ∀ t, 0 ≤ t → 9/10 ≤ a t ∧ a t ≤ 11/10 := by
  have hl := scalar_lower_barrier a (fun t => 1-a t) (9/10) hd h0.1
    (fun t _ h => by linarith)
  have hu := scalar_upper_barrier a (fun t => 1-a t) (11/10) hd h0.2
    (fun t _ h => by linarith)
  exact fun t ht => ⟨hl t ht,hu t ht⟩

theorem scalar_material_interior (a : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt a (1-a t) t)
    (h0 : 9/10 ≤ a 0 ∧ a 0 ≤ 11/10) :
    ∀ t, 4 ≤ t → 159/160 ≤ a t ∧ a t ≤ 161/160 := by
  intro t ht
  have he4 : 16 ≤ Real.exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have het : 16 ≤ Real.exp t := he4.trans (Real.exp_le_exp.mpr ht)
  have hi : Real.exp (-t) ≤ 1/16 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos t)).2
    linarith
  have hpos : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hlo := mul_le_mul_of_nonneg_right h0.1 hpos
  have hup := mul_le_mul_of_nonneg_right h0.2 hpos
  rw [affine_material_solution a hd t (by linarith)]
  constructor <;> nlinarith

end
end ProductiveRecovery
