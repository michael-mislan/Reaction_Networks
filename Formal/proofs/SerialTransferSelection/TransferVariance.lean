import proofs.SerialTransferSelection.TransferCentered

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

noncomputable def weightedSubsetTotal (L M : ℕ) (w : Fin L → ℝ) (S : TransferSubset L M) : ℝ :=
  ∑ i, subsetIndicator i S*w i

theorem weightedSubsetTotal_mean (L M : ℕ) (hM : M ≤ L) (w : Fin L → ℝ) :
    (uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w)=
      ∑ i, (uniformTransferLaw L M hM).expect (subsetIndicator i)*w i := by
  unfold weightedSubsetTotal
  rw [finiteLaw_expect_sum]
  simp_rw [finiteLaw_expect_mul_const]

theorem weightedSubsetTotal_center (L M : ℕ) (hM : M ≤ L) (w : Fin L → ℝ) (S : TransferSubset L M) :
    weightedSubsetTotal L M w S-(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w)=
      ∑ i, w i*centeredSubsetIndicator L M hM i S := by
  rw [weightedSubsetTotal_mean]
  unfold weightedSubsetTotal centeredSubsetIndicator
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weighted_subset_variance_bound (L M : ℕ) (hL : 2 ≤ L) (hM : M ≤ L)
    (w : Fin L → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) :
    (uniformTransferLaw L M hM).expect (fun S =>
      (weightedSubsetTotal L M w S-(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w))^2) ≤
      (uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w) := by
  classical
  let μ := uniformTransferLaw L M hM
  have hf (S : TransferSubset L M) :
      (weightedSubsetTotal L M w S-μ.expect (weightedSubsetTotal L M w))^2=
      ∑ i : Fin L, ∑ j : Fin L, (w i*w j)*
        (centeredSubsetIndicator L M hM i S*centeredSubsetIndicator L M hM j S) := by
    rw [weightedSubsetTotal_center,pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only [μ] at hf
  simp_rw [hf,finiteLaw_expect_sum,finiteLaw_expect_const_mul]
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L))) (fun i _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L))) (fun j _ =>
      mul_le_mul_of_nonneg_left (centered_subset_pair_bound L M hL hM i j)
        (mul_nonneg (hw i).1 (hw j).1)))
  apply hb.trans
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [weightedSubsetTotal_mean]
  apply Finset.sum_le_sum
  intro i _
  have hp := (subset_marginal_bounds L M hM i).1
  have hwi : w i*w i ≤ w i := by nlinarith only [(hw i).1,(hw i).2]
  nlinarith only [mul_le_mul_of_nonneg_left hwi hp]

end SerialTransferSelection
