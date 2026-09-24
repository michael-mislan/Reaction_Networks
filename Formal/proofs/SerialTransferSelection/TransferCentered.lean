import proofs.SerialTransferSelection.TransferCovariance

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

theorem finiteLaw_expect_add {α : Type*} [Fintype α] (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x+g x)=μ.expect f+μ.expect g := by
  simp only [FiniteLaw.expect,mul_add,Finset.sum_add_distrib]

theorem finiteLaw_expect_sub {α : Type*} [Fintype α] (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x-g x)=μ.expect f-μ.expect g := by
  simp only [FiniteLaw.expect,mul_sub,Finset.sum_sub_distrib]

theorem finiteLaw_expect_const_mul {α : Type*} [Fintype α] (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c*f x)=c*μ.expect f := by
  simpa only [mul_comm c] using finiteLaw_expect_mul_const μ f c

theorem finiteLaw_covariance_identity {α : Type*} [Fintype α] (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => (f x-μ.expect f)*(g x-μ.expect g))=
      μ.expect (fun x => f x*g x)-μ.expect f*μ.expect g := by
  have hf : (fun x => (f x-μ.expect f)*(g x-μ.expect g))=
      fun x => (f x*g x-f x*μ.expect g)-μ.expect f*g x+μ.expect f*μ.expect g := by
    funext x
    ring
  rw [hf,finiteLaw_expect_add,finiteLaw_expect_sub,finiteLaw_expect_sub,
    finiteLaw_expect_mul_const,finiteLaw_expect_const_mul,FiniteLaw.expect_const]
  ring

noncomputable def centeredSubsetIndicator (L M : ℕ) (hM : M ≤ L) (i : Fin L)
    (S : TransferSubset L M) : ℝ :=
  subsetIndicator i S-(uniformTransferLaw L M hM).expect (subsetIndicator i)

theorem centered_subset_pair_bound (L M : ℕ) (hL : 2 ≤ L) (hM : M ≤ L) (i j : Fin L) :
    (uniformTransferLaw L M hM).expect
      (fun S => centeredSubsetIndicator L M hM i S*centeredSubsetIndicator L M hM j S) ≤
      if i=j then (uniformTransferLaw L M hM).expect (subsetIndicator i) else 0 := by
  classical
  unfold centeredSubsetIndicator
  rw [finiteLaw_covariance_identity]
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    have hf : (fun S : TransferSubset L M => subsetIndicator i S*subsetIndicator i S)=subsetIndicator i := by
      funext S
      exact subsetIndicator_square L M i S
    rw [hf]
    nlinarith only [sq_nonneg ((uniformTransferLaw L M hM).expect (subsetIndicator i))]
  · rw [if_neg hij]
    exact sub_nonpos.mpr (subset_pair_covariance_nonpos L M hL hM i j hij)

end SerialTransferSelection
