import proofs.SerialTransferSelection.TransferMoments

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

theorem subset_marginal_bounds (L M : ℕ) (hM : M ≤ L) (i : Fin L) :
    0 ≤ (uniformTransferLaw L M hM).expect (subsetIndicator i) ∧
      (uniformTransferLaw L M hM).expect (subsetIndicator i) ≤ 1 := by
  let μ := uniformTransferLaw L M hM
  have h0 := μ.expect_mono (fun _ => 0) (subsetIndicator i)
    (by intro S; unfold subsetIndicator; split_ifs <;> norm_num)
  have h1 := μ.expect_mono (subsetIndicator i) (fun _ => 1)
    (by intro S; unfold subsetIndicator; split_ifs <;> norm_num)
  simpa only [FiniteLaw.expect_const] using And.intro h0 h1

theorem subset_pair_covariance_nonpos (L M : ℕ) (hL : 2 ≤ L) (hM : M ≤ L)
    (i j : Fin L) (hij : i ≠ j) :
    (uniformTransferLaw L M hM).expect (fun S => subsetIndicator i S*subsetIndicator j S) ≤
      (uniformTransferLaw L M hM).expect (subsetIndicator i)*
      (uniformTransferLaw L M hM).expect (subsetIndicator j) := by
  rw [subset_marginals_equal L M hM j i]
  let p := (uniformTransferLaw L M hM).expect (subsetIndicator i)
  let r := (uniformTransferLaw L M hM).expect (fun S => subsetIndicator i S*subsetIndicator j S)
  have hp := subset_marginal_bounds L M hM i
  have hm := subset_marginal_total L M hM i
  have hr := subset_pair_row L M hM i j hij
  have hmp := congrArg (fun x : ℝ => x*p) hm
  have hp2 : p*p ≤ p := by nlinarith only [hp.1,hp.2]
  have hLpos : 0 < (L : ℝ)-1 := by exact_mod_cast (by omega : 0 < (L : ℤ)-1)
  change r ≤ p*p
  apply (mul_le_mul_iff_right₀ hLpos).mp
  dsimp only [p,r] at hmp ⊢
  nlinarith only [hr,hmp,hp2]

end SerialTransferSelection
