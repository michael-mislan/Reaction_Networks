import proofs.DynamicSharedResource.RectangularBounds

namespace DynamicSharedResource.Certificate
noncomputable section
open scoped BigOperators

def faceBudget (q : State) (i : Fin 8) : ℝ :=
  A i i*q i+(∑ j ∈ Finset.univ.erase i, |A i j| *q j)+|b i|+nb i

theorem rectangular_source_faces (q a : State) (hq : ∀ i, q i ≤ 1)
    (ha : InRect q a) (i : Fin 8) :
    (a i=q i → modalField a i ≤ faceBudget q i) ∧
    (a i= -q i → -faceBudget q i ≤ modalField a i) := by
  have hc : InCube 1 a := fun j => (ha j).trans (hq j)
  have hr := abs_le.mp (modal_remainder 1 (by norm_num) le_rfl a hc i)
  norm_num only [one_pow,mul_one] at hr
  have hsplit : A.mulVec a i = A i i*a i + ∑ j ∈ Finset.univ.erase i, A i j*a j :=
    (Finset.add_sum_erase Finset.univ (fun j => A i j*a j) (Finset.mem_univ i)).symm
  have hoff : |∑ j ∈ Finset.univ.erase i, A i j*a j| ≤
      ∑ j ∈ Finset.univ.erase i, |A i j| *q j := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j*a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _)
  have ho := abs_le.mp hoff
  rw [hsplit] at hr
  unfold faceBudget
  constructor
  · intro hai
    rw [hai] at hr
    linarith [le_abs_self (b i)]
  · intro hai
    rw [hai] at hr
    nlinarith [neg_abs_le (b i)]

theorem faceBudget_affine (r s : State) (t : ℝ) (i : Fin 8) :
    faceBudget ((1-t) • r+t • s) i = (1-t)*faceBudget r i+t*faceBudget s i := by
  simp only [faceBudget,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,
    Finset.sum_add_distrib]
  simp_rw [← mul_assoc, mul_comm (|A i _|) (1-t), mul_comm (|A i _|) t,
    mul_assoc, ← Finset.mul_sum]
  ring

end
end DynamicSharedResource.Certificate
