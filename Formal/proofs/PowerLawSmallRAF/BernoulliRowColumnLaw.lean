import proofs.PowerLawSmallRAF.ProductRowCoupling

namespace PowerLawSmallRAF
open scoped BigOperators
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
set_option maxHeartbeats 100000

def inhomogeneousSubsetWeight (p : I → ℝ) (A : Finset I) : ℝ :=
  (∏ i ∈ A, p i)*(∏ i ∈ Aᶜ, (1-p i))

omit [Fintype J] [DecidableEq J] in
theorem inhomogeneousSubsetWeight_eq_prod (p : I → ℝ) (A : Finset I) :
    inhomogeneousSubsetWeight p A = ∏ i, if i ∈ A then p i else 1-p i := by
  rw [← Finset.prod_mul_prod_compl A (fun i => if i ∈ A then p i else 1-p i)]
  unfold inhomogeneousSubsetWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [if_pos hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hia : i ∉ A := Finset.mem_compl.mp hi
    simp only [if_neg hia]

omit [Fintype J] [DecidableEq J] in
theorem inhomogeneousSubsetWeight_const (p : ℝ) (A : Finset I) :
    inhomogeneousSubsetWeight (fun _ => p) A = bernoulliSubsetRowWeight p A := by
  simp only [inhomogeneousSubsetWeight, Finset.prod_const, Finset.card_compl, bernoulliSubsetRowWeight]

omit [Fintype J] [DecidableEq J] in
theorem inhomogeneousSubsetWeight_sum (p : I → ℝ) :
    (∑ A : Finset I, inhomogeneousSubsetWeight p A) = 1 := by
  simp only [inhomogeneousSubsetWeight]
  rw [← Fintype.prod_add p (fun i => 1-p i)]
  simp

omit [Fintype J] [DecidableEq J] in
theorem inhomogeneousSubsetWeight_empty (p : I → ℝ) :
    inhomogeneousSubsetWeight p ∅ = ∏ i, (1-p i) := by
  simp only [inhomogeneousSubsetWeight, Finset.prod_empty, Finset.compl_empty, one_mul]

def bernoulliRowTranspose (B : I → Finset J) : J → Finset I :=
  fun j => Finset.univ.filter fun i => j ∈ B i

theorem bernoulliRowTranspose_involution (B : I → Finset J) :
    bernoulliRowTranspose (bernoulliRowTranspose B) = B := by
  funext i
  ext j
  simp [bernoulliRowTranspose]

def bernoulliRowColumnEquiv : (I → Finset J) ≃ (J → Finset I) where
  toFun := bernoulliRowTranspose
  invFun := bernoulliRowTranspose
  left_inv := bernoulliRowTranspose_involution
  right_inv := bernoulliRowTranspose_involution

theorem bernoulliRowsWeight_transpose (p : I → ℝ) (B : I → Finset J) :
    bernoulliRowsWeight p B =
      ∏ j : J, inhomogeneousSubsetWeight p (bernoulliRowTranspose B j) := by
  unfold bernoulliRowsWeight
  simp_rw [← inhomogeneousSubsetWeight_const, inhomogeneousSubsetWeight_eq_prod]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  simp only [bernoulliRowTranspose, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exact reindexing of every observable, conditional on a fixed row parameter
vector. Its right-hand side is a product over independent channel columns. -/
theorem bernoulliRows_column_expectation (p : I → ℝ) (F : (J → Finset I) → ℝ) :
    (∑ B : I → Finset J, bernoulliRowsWeight p B * F (bernoulliRowTranspose B)) =
      ∑ C : J → Finset I, (∏ j, inhomogeneousSubsetWeight p (C j))*F C := by
  apply Fintype.sum_equiv bernoulliRowColumnEquiv
  intro B
  rw [bernoulliRowsWeight_transpose]
  rfl

end
end PowerLawSmallRAF
