import proofs.SerialTransferSelection.TransferSymmetry

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

theorem finiteLaw_expect_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.expect (fun x => ∑ i, f i x)=∑ i, μ.expect (f i) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem finiteLaw_expect_mul_const {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun x => f x*c)=μ.expect f*c := by
  unfold FiniteLaw.expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem subsetIndicator_sum (L M : ℕ) (S : TransferSubset L M) :
    (∑ i : Fin L, subsetIndicator i S)=(M : ℝ) := by
  classical
  simp [subsetIndicator,S.property]

theorem subsetIndicator_square (L M : ℕ) (i : Fin L) (S : TransferSubset L M) :
    subsetIndicator i S*subsetIndicator i S=subsetIndicator i S := by
  unfold subsetIndicator
  split_ifs <;> norm_num

theorem subset_marginal_total (L M : ℕ) (hM : M ≤ L) (i : Fin L) :
    (L : ℝ)*(uniformTransferLaw L M hM).expect (subsetIndicator i)=(M : ℝ) := by
  let μ := uniformTransferLaw L M hM
  have h := finiteLaw_expect_sum μ (fun j => subsetIndicator j)
  have heq (j : Fin L) : μ.expect (subsetIndicator j)=μ.expect (subsetIndicator i) :=
    subset_marginals_equal L M hM j i
  simp_rw [heq] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hf : (fun S : TransferSubset L M => ∑ j : Fin L, subsetIndicator j S)=fun _ => (M : ℝ) := by
    funext S
    exact subsetIndicator_sum L M S
  rw [hf,FiniteLaw.expect_const] at h
  exact h.symm

theorem subset_pair_row (L M : ℕ) (hM : M ≤ L) (i j : Fin L) (hij : i ≠ j) :
    ((L : ℝ)-1)*(uniformTransferLaw L M hM).expect
      (fun S => subsetIndicator i S*subsetIndicator j S)=
      ((M : ℝ)-1)*(uniformTransferLaw L M hM).expect (subsetIndicator i) := by
  classical
  let μ := uniformTransferLaw L M hM
  let p := μ.expect (subsetIndicator i)
  let r := μ.expect (fun S => subsetIndicator i S*subsetIndicator j S)
  have h := finiteLaw_expect_sum μ (fun k S => subsetIndicator i S*subsetIndicator k S)
  have hf : (fun S : TransferSubset L M => ∑ k : Fin L, subsetIndicator i S*subsetIndicator k S)=
      fun S => subsetIndicator i S*(M : ℝ) := by
    funext S
    rw [← Finset.mul_sum,subsetIndicator_sum]
  rw [hf,finiteLaw_expect_mul_const] at h
  have hterm (k : Fin L) : μ.expect (fun S => subsetIndicator i S*subsetIndicator k S)=
      if k=i then p else r := by
    by_cases hk : k=i
    · subst k
      simp only [if_true]
      congr 1
      funext S
      exact subsetIndicator_square L M i S
    · rw [if_neg hk]
      exact subset_pair_swap L M hM i k j (Ne.symm hk) hij
  simp_rw [hterm] at h
  have hsum : (∑ k : Fin L, if k=i then p else r)=p+((L : ℝ)-1)*r := by
    have ht (k : Fin L) : (if k=i then p else r)=r+(if k=i then p-r else 0) := by
      split_ifs <;> ring
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring
  rw [hsum] at h
  change ((L : ℝ)-1)*r=((M : ℝ)-1)*p
  change p*(M : ℝ)=p+((L : ℝ)-1)*r at h
  nlinarith only [h]

end SerialTransferSelection
