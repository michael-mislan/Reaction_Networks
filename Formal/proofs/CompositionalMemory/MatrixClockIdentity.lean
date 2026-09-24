import proofs.CompositionalMemory.KernelMatrixExponential

namespace CompositionalMemory
open FiniteCopy
open scoped Matrix.Norms.Operator

theorem matrix_exp_scalar_shift {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (A : Matrix α α ℝ) :
    NormedSpace.exp (c • (1 : Matrix α α ℝ)+A) = Real.exp c • NormedSpace.exp A := by
  have hc : Commute (c • (1 : Matrix α α ℝ)) A := by
    unfold Commute SemiconjBy
    simp
  rw [Matrix.exp_add_of_commute _ _ hc]
  have hs : NormedSpace.exp (c • (1 : Matrix α α ℝ)) =
      Real.exp c • (1 : Matrix α α ℝ) := by
    simpa only [Algebra.algebraMap_eq_smul_one,Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix α α ℝ) c).symm
  rw [hs]
  simp

theorem kernel_poissonized_generator_matrix {α : Type*} [Fintype α] [DecidableEq α]
    (P : FiniteKernel α) (t : NNReal) (f : α → ℝ) (x : α) :
    P.poissonized t f x =
      (NormedSpace.exp ((t : ℝ) • (kernelMatrix P-1))).mulVec f x := by
  rw [kernel_poissonized_matrix]
  have hm : (t : ℝ) • (kernelMatrix P-1) =
      (-(t : ℝ)) • (1 : Matrix α α ℝ)+(t : ℝ) • kernelMatrix P := by
    simp [sub_eq_add_neg,add_comm]
  rw [hm,matrix_exp_scalar_shift]
  simp [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]

noncomputable def jumpGeneratorMatrix {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) : Matrix α α ℝ :=
  fun x y => M.generator (fun z => if z=y then 1 else 0) x

theorem uniformize_generator_matrix {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q) (hb : ∀ x, M.total x ≤ q) :
    q • (kernelMatrix (M.uniformize q hq hb)-1) = jumpGeneratorMatrix M := by
  ext x y
  have h := M.uniformize_step q hq hb (fun z => if z=y then 1 else 0) x
  simp only [FiniteKernel.step,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at h
  change q*((M.uniformize q hq hb).prob x y-(1 : Matrix α α ℝ) x y) = _
  rw [h]
  simp only [Matrix.one_apply,jumpGeneratorMatrix]
  field_simp
  ring

theorem uniformized_law_generator_matrix {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hb : ∀ x, M.total x ≤ q) (f : α → ℝ) (x : α) :
    (M.uniformize q hq hb).poissonized (q*t) f x =
      (NormedSpace.exp ((t : ℝ) • jumpGeneratorMatrix M)).mulVec f x := by
  rw [kernel_poissonized_generator_matrix]
  rw [NNReal.coe_mul,mul_comm (q : ℝ),mul_smul,uniformize_generator_matrix]

theorem uniformized_clock_independent {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (q r t : NNReal)
    (hq : 0 < (q : ℝ)) (hr : 0 < (r : ℝ))
    (hQ : ∀ x, M.total x ≤ q) (hR : ∀ x, M.total x ≤ r) (f : α → ℝ) (x : α) :
    (M.uniformize q hq hQ).poissonized (q*t) f x =
      (M.uniformize r hr hR).poissonized (r*t) f x := by
  rw [uniformized_law_generator_matrix,uniformized_law_generator_matrix]

end CompositionalMemory
