import proofs.DynamicSharedResource.Algebra
import proofs.DynamicSharedResource.Bounds

namespace DynamicSharedResource
noncomputable section
open scoped BigOperators

def productBounds (w : State) : Fin 5 → ℝ :=
  ![w 0*w 1,w 0*w 4,(2*w 1+w 3)*w 2,(2*w 1+w 3)*w 3,w 4*w 7]

theorem products_bound (d w : State) (q : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hq : 0 ≤ q) (hd : ∀ i, |d i| ≤ w i*q) (j : Fin 5) :
    |products d j| ≤ productBounds w j*q^2 := by
  have hg : |-2*d 1-d 3| ≤ (2*w 1+w 3)*q := by
    calc
      |-2*d 1-d 3| ≤ |-2*d 1| +|d 3| := abs_sub _ _
      _ ≤ 2*(w 1*q)+w 3*q := by
        rw [abs_mul]
        norm_num
        linarith [hd 1,hd 3]
      _ = (2*w 1+w 3)*q := by ring
  have hg0 : 0 ≤ 2*w 1+w 3 := by linarith [hw 1,hw 3]
  fin_cases j
  · exact abs_product_le _ _ _ _ _ (hw 0) (hw 1) hq (hd 0) (hd 1)
  · exact abs_product_le _ _ _ _ _ (hw 0) (hw 4) hq (hd 0) (hd 4)
  · exact abs_product_le _ _ _ _ _ hg0 (hw 2) hq hg (hd 2)
  · exact abs_product_le _ _ _ _ _ hg0 (hw 3) hq hg (hd 3)
  · exact abs_product_le _ _ _ _ _ (hw 4) (hw 7) hq (hd 4) (hd 7)

theorem sum_products_bound {n : ℕ} (v p P : Fin n → ℝ) (q : ℝ)
    (hp : ∀ j, |p j| ≤ P j*q^2) :
    |∑ j, v j*p j| ≤ (∑ j, |v j| *P j)*q^2 := by
  calc
    _ ≤ ∑ j, |v j*p j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |v j| *(P j*q^2) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hp j) (abs_nonneg _)
    _ = _ := by simp only [← mul_assoc,Finset.sum_mul]

theorem source_remainder_bound (c d w : State) (q : ℝ)
    (hw : 0 ≤ w 0) (_hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hd : |d 0| ≤ w 0*q) (hden : 0 < 873/10-c 0-w 0) :
    |sourceRemainder c d| ≤
      (45*(573/10)*(w 0)^2/((873/10-c 0)^2*(873/10-c 0-w 0)))*q^2 := by
  have hdw : |d 0| ≤ w 0 := hd.trans (mul_le_of_le_one_right hw hq1)
  have hdpos : 0 < 873/10-c 0-d 0 := by linarith [le_abs_self (d 0)]
  have hcpos : 0 < 873/10-c 0 := by linarith
  have hdsq : (d 0)^2 ≤ (w 0)^2*q^2 := by
    nlinarith [sq_abs (d 0),mul_self_le_mul_self (abs_nonneg (d 0)) hd]
  have hdenle : (873/10-c 0)^2*(873/10-c 0-w 0) ≤
      (873/10-c 0)^2*(873/10-c 0-d 0) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith [le_abs_self (d 0)]
  have hsmall : 0 < (873/10-c 0)^2*(873/10-c 0-w 0) :=
    mul_pos (sq_pos_of_pos hcpos) hden
  have hlarge : 0 < (873/10-c 0)^2*(873/10-c 0-d 0) :=
    mul_pos (sq_pos_of_pos hcpos) hdpos
  have heq : |sourceRemainder c d| =
      45*(573/10)*(d 0)^2/((873/10-c 0)^2*(873/10-c 0-d 0)) := by
    unfold sourceRemainder
    rw [abs_div,abs_of_pos hlarge]
    have hn : -45*(573/10)*(d 0)^2 ≤ 0 := by nlinarith [sq_nonneg (d 0)]
    rw [abs_of_nonpos hn]
    ring
  rw [heq]
  calc
    _ ≤ 45*(573/10)*((w 0)^2*q^2)/((873/10-c 0)^2*(873/10-c 0-w 0)) := by
      apply div_le_div₀ (by positivity) (by nlinarith) hsmall hdenle
    _ = _ := by ring

end
end DynamicSharedResource
