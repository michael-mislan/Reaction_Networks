import proofs.FiniteCopy.KernelExpectations

namespace CompositionalMemory
open FiniteCopy
open scoped Matrix.Norms.Operator

noncomputable def kernelMatrix {α : Type*} [Fintype α] (P : FiniteKernel α) :
    Matrix α α ℝ := P.prob

theorem kernel_steps_matrix {α : Type*} [Fintype α] [DecidableEq α]
    (P : FiniteKernel α) (n : ℕ) (f : α → ℝ) :
    P.steps n f = ((kernelMatrix P)^n).mulVec f := by
  induction n with
  | zero => simp [FiniteKernel.steps]
  | succ n ih =>
    change (fun x => (kernelMatrix P).mulVec (P.steps n f) x) = _
    rw [ih,Matrix.mulVec_mulVec,pow_succ']

noncomputable def matrixObservable {α : Type*} [Fintype α]
    (f : α → ℝ) (x : α) : Matrix α α ℝ →L[ℝ] ℝ where
  toFun A := ∑ y, A x y*f y
  map_add' A B := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c A := by simp [Finset.mul_sum,mul_assoc]
  cont := by fun_prop

theorem kernel_poissonized_matrix {α : Type*} [Fintype α] [DecidableEq α]
    (P : FiniteKernel α) (t : NNReal) (f : α → ℝ) (x : α) :
    P.poissonized t f x = Real.exp (-(t : ℝ))*
      (NormedSpace.exp ((t : ℝ) • (kernelMatrix P))).mulVec f x := by
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    ((t : ℝ) • (kernelMatrix P))).mapL (matrixObservable f x)
  have ht := hs.mul_left (Real.exp (-(t : ℝ)))
  have he (n : ℕ) : Real.exp (-(t : ℝ))*
      matrixObservable f x ((n.factorial : ℝ)⁻¹ • ((t : ℝ) • (kernelMatrix P))^n) =
      poissonWeight t n*P.steps n f x := by
    rw [kernel_steps_matrix]
    simp only [smul_pow,matrixObservable,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,
      AddHom.coe_mk,Matrix.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,
      poissonWeight]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [he] at ht
  exact ht.tsum_eq

end CompositionalMemory

