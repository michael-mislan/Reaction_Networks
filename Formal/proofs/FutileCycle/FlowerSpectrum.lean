import proofs.FutileCycle.FlowerMatrix
import proofs.DUnstableCores.DScaling

namespace FutileCycle
noncomputable section
open Matrix DUnstableCores

def flowerComplex (k : ℕ) : Matrix (FlowerIndex k) (FlowerIndex k) ℂ :=
  (flowerMatrix k).map (Int.castRingHom ℂ)

theorem flower_hub (k : ℕ) (u : FlowerIndex k → ℂ) :
    (flowerComplex k *ᵥ u) (.inl 0) =
      u (.inl (Fin.last k)) - u (.inl 0) + u (.inr ()) := by
  simp [flowerComplex, flowerMatrix, cycleReduced, flowerSpoke, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, sub_mul, Finset.sum_sub_distrib, Matrix.mul_apply]

theorem flower_step (k : ℕ) (i : Fin k) (u : FlowerIndex k → ℂ) :
    (flowerComplex k *ᵥ u) (.inl i.succ) = u (.inl i.castSucc) - u (.inl i.succ) := by
  have he (j : Fin (k+1)) : j.val=i.val ↔ j=i.castSucc := by
    simp [Fin.ext_iff]
  simp [flowerComplex, flowerMatrix, cycleReduced, flowerSpoke, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, he, sub_mul, Finset.sum_sub_distrib, Matrix.mul_apply]

theorem flower_leaf (k : ℕ) (u : FlowerIndex k → ℂ) :
    (flowerComplex k *ᵥ u) (.inr ()) = u (.inl 0) - u (.inr ()) := by
  simp [flowerComplex, flowerMatrix, flowerSpoke, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]

theorem flower_real_root (k : ℕ) (hk : 2 ≤ k) :
    ∃ w : ℝ, 1 < w ∧ w^(k+1) - w^(k-1) - 1 = 0 := by
  let f : ℝ → ℝ := fun w => w^(k+1) - w^(k-1) - 1
  have hc : Continuous f := by fun_prop
  have hf1 : f 1 = -1 := by simp [f]
  have hpow : (2:ℝ)^(k+1) = 4 * 2^(k-1) := by
    have he : k+1=(k-1)+2 := by omega
    rw [he, pow_add]
    ring
  have hf2 : 0 ≤ f 2 := by
    have hp : (1:ℝ) ≤ 2^(k-1) := one_le_pow₀ (by norm_num)
    dsimp [f]
    nlinarith
  obtain ⟨w,hw,hew⟩ := intermediate_value_Icc (by norm_num : (1:ℝ)≤2)
    hc.continuousOn (show (0:ℝ) ∈ Set.Icc (f 1) (f 2) by rw [hf1]; exact ⟨by norm_num,hf2⟩)
  refine ⟨w,?_,hew⟩
  have hne : w ≠ 1 := by intro hh; subst w; rw [hf1] at hew; norm_num at hew
  exact lt_of_le_of_ne hw.1 (Ne.symm hne)

theorem flower_eigenpair (k : ℕ) (hk : 2 ≤ k) :
    ∃ z : ℂ, ∃ u : FlowerIndex k → ℂ, 0 < z.re ∧ u ≠ 0 ∧
      flowerComplex k *ᵥ u = z • u := by
  obtain ⟨w,hw,hq⟩ := flower_real_root k hk
  let u : FlowerIndex k → ℂ := Sum.elim (fun i => (w:ℂ)^(k-i.val))
    (fun _ => (w:ℂ)^(k-1))
  have hqc : (w:ℂ)^(k+1) - (w:ℂ)^(k-1) - 1 = 0 := by exact_mod_cast hq
  refine ⟨(w:ℂ)-1,u,by simpa using sub_pos.mpr hw,?_,?_⟩
  · intro hh
    have hh' := congrFun hh (.inl (Fin.last k))
    simp [u] at hh'
  · funext i
    cases i with
    | inl i =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [flower_hub]
        simp only [u, Sum.elim_inl, Sum.elim_inr, Fin.val_zero, Nat.sub_zero,
          Fin.val_last, Nat.sub_self, pow_zero, Pi.smul_apply, smul_eq_mul]
        rw [pow_succ] at hqc
        linear_combination -hqc
      · rw [flower_step]
        simp only [u, Sum.elim_inl, Fin.val_castSucc, Fin.val_succ,
          Pi.smul_apply, smul_eq_mul]
        have he : k-j.val=(k-(j.val+1))+1 := by omega
        rw [he, pow_succ]
        ring
    | inr i =>
      cases i
      rw [flower_leaf]
      simp only [u, Sum.elim_inl, Sum.elim_inr, Fin.val_zero, Nat.sub_zero,
        Pi.smul_apply, smul_eq_mul]
      have he : k=(k-1)+1 := by omega
      conv_lhs => arg 1; rw [he, pow_succ]
      ring

theorem flower_unstable (k : ℕ) (hk : 2 ≤ k) :
    HurwitzUnstable ((flowerMatrix k).map (fun x : ℤ => (x:ℝ))) := by
  obtain ⟨z,u,hz,hu,he⟩ := flower_eigenpair k hk
  refine ⟨z,u,hz,hu,?_⟩
  intro i
  have hmat : complexify ((flowerMatrix k).map (fun x : ℤ => (x:ℝ))) =
      flowerComplex k := by ext a b; simp [complexify, flowerComplex]
  rw [hmat]
  exact congrFun he i

end
end FutileCycle
