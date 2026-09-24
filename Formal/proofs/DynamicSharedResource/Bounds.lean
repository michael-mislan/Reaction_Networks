import proofs.DynamicSharedResource.BoxFlow

namespace DynamicSharedResource
noncomputable section
open scoped BigOperators

theorem abs_mulVec_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (a : Fin n → ℝ) (q : ℝ) (ha : ∀ j, |a j| ≤ q) (i : Fin m) :
    |M.mulVec a i| ≤ (∑ j, |M i j|)*q := by
  calc
    |M.mulVec a i| ≤ ∑ j, |M i j*a j| := by
      simpa only [Matrix.mulVec,dotProduct] using
        Finset.abs_sum_le_sum_abs (fun j => M i j*a j) Finset.univ
    _ ≤ ∑ j, |M i j| *q := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _)
    _ = (∑ j, |M i j|)*q := (Finset.sum_mul ..).symm

theorem abs_product_le (x y X Y q : ℝ) (hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (hq : 0 ≤ q) (hx : |x| ≤ X*q) (hy : |y| ≤ Y*q) :
    |x*y| ≤ (X*Y)*q^2 := by
  rw [abs_mul]
  calc
    |x| *|y| ≤ (X*q)*(Y*q) := mul_le_mul hx hy (abs_nonneg _) (mul_nonneg hX hq)
    _ = (X*Y)*q^2 := by ring

/-- A finite matrix and quadratic remainder certificate implies inward motion.
The constant residual is retained, using q>=1/2. -/
theorem faceDecay_of_bounds (f : State → State) (A : Matrix (Fin 8) (Fin 8) ℝ)
    (b n : State) (hn : ∀ i, 0 ≤ n i)
    (hrem : ∀ q, (1/2:ℝ) ≤ q → q ≤ 1 → ∀ a, InCube q a → ∀ i,
      |f a i-b i-A.mulVec a i| ≤ n i*q^2)
    (hcert : ∀ i, A i i + (∑ j ∈ Finset.univ.erase i, |A i j|) + n i + 2*|b i| < -(1/2000:ℝ)) :
    FaceDecay f := by
  intro q hq hq1 a ha i
  have hqpos : 0 < q := by linarith
  have hq2 : q^2 ≤ q := by nlinarith
  have hr := abs_le.mp (hrem q hq hq1 a ha i)
  have hsplit : A.mulVec a i = A i i*a i + ∑ j ∈ Finset.univ.erase i, A i j*a j := by
    exact (Finset.add_sum_erase Finset.univ (fun j => A i j*a j) (Finset.mem_univ i)).symm
  have hoff : |∑ j ∈ Finset.univ.erase i, A i j*a j| ≤
      (∑ j ∈ Finset.univ.erase i, |A i j|)*q := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j*a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j| *q := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (ha j) (abs_nonneg _)
      _ = _ := (Finset.sum_mul ..).symm
  have hb : |b i| ≤ 2*|b i| *q := by nlinarith [abs_nonneg (b i)]
  have hnq := mul_le_mul_of_nonneg_left hq2 (hn i)
  have hfinal := mul_lt_mul_of_pos_right (hcert i) hqpos
  have ho := abs_le.mp hoff
  rw [hsplit] at hr
  constructor
  · intro hai
    rw [hai] at hr
    nlinarith [le_abs_self (b i)]
  · intro hai
    rw [hai] at hr
    nlinarith [neg_abs_le (b i)]

end
end DynamicSharedResource
