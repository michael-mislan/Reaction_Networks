import proofs.RAF1519.Reservoir.AffineBounds

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators Matrix

def quadraticRate {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (v y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, P i j*(v i*y j+y i*v j)

theorem quadratic_deriv {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) (X : ℝ → Fin n → ℝ) (v : Fin n → ℝ) (t : ℝ)
    (hX : HasDerivAt X v t) :
    HasDerivAt (fun t => quadratic P (X t-c)) (quadraticRate P v (X t-c)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((hasDerivAt_pi.1 hX i).sub_const (c i)).mul
        ((hasDerivAt_pi.1 hX j).sub_const (c j))).const_mul (P i j)))
  simpa only [quadratic,quadraticRate,Pi.sub_apply,mul_assoc] using hd

theorem quadratic_contDiff {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ContDiff ℝ 1 (fun x => quadratic P (x-c)) := by
  unfold quadratic
  fun_prop

theorem quadratic_fderiv {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (c x v : Fin n → ℝ) :
    fderiv ℝ (fun x => quadratic P (x-c)) x v = quadraticRate P v (x-c) := by
  have hg : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [Pi.add_apply,zero_add,one_smul] using
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have hq := ((quadratic_contDiff P c).differentiable (by norm_num) x).hasFDerivAt
  have hq' : HasFDerivAt (fun x => quadratic P (x-c))
      (fderiv ℝ (fun x => quadratic P (x-c)) x) ((fun t : ℝ => x+t • v) 0) := by
    simpa only [zero_smul,add_zero] using hq
  have hc := hq'.comp_hasDerivAt (0:ℝ) hg
  have hd := quadratic_deriv P c (fun t : ℝ => x+t • v) v 0 hg
  simpa only [zero_smul,add_zero] using hc.unique hd

theorem quadratic_dot {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    quadratic P y = y ⬝ᵥ (P *ᵥ y) := by
  unfold quadratic Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticRate_dot {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (v y : Fin n → ℝ) :
    quadraticRate P v y = v ⬝ᵥ (P *ᵥ y)+y ⬝ᵥ (P *ᵥ v) := by
  unfold quadraticRate Matrix.mulVec dotProduct
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticRate_matrix {n : ℕ} (P J : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    quadraticRate P (J *ᵥ y) y = -quadratic (-(P*J+J.transpose*P)) y := by
  rw [quadraticRate_dot,quadratic_dot]
  simp only [Matrix.neg_mulVec,dotProduct_neg,neg_neg,Matrix.add_mulVec,
    dotProduct_add,← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm (P *ᵥ y) (J *ᵥ y)]
  ring

theorem quadratic_upper {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (hrow : ∀ i, (∑ j, |P i j|)+(∑ j, |P j i|) ≤ 400) :
    quadratic P y ≤ 200*(∑ i, (y i)^2) := by
  have h := CoreCouplingCAC.comparison_energy_bound P (fun i j => |P i j|)
    (fun _ => 1) (fun _ => 1) y (-400) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun i => le_abs_self _)
    (fun _ _ _ => le_rfl) (fun i => by simpa using hrow i)
  have he : (∑ i, ∑ j, 2*(1:ℝ)*P i j*1*y i*y j) = 2*quadratic P y := by
    unfold quadratic
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  simp only [one_mul,mul_one] at h
  linarith

end
end RAF1519.Reservoir
