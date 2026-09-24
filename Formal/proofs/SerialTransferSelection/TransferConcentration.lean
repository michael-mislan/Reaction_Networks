import proofs.SerialTransferSelection.TransferVariance

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

noncomputable def weightedTransferBad (L M : ℕ) (hM : M ≤ L) (w : Fin L → ℝ) (ε : ℝ) :
    Set (TransferSubset L M) :=
  {S | (ε*(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w))^2 <
    (weightedSubsetTotal L M w S-(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w))^2}

theorem finiteLaw_squared_markov {α : Type*} [Fintype α] (μ : FiniteLaw α) (f : α → ℝ) (a : ℝ) :
    a*μ.expect (FiniteKernel.eventIndicator {x | a < (f x)^2}) ≤ μ.expect (fun x => (f x)^2) := by
  classical
  have h := μ.expect_mono (fun x => a*FiniteKernel.eventIndicator {x | a < (f x)^2} x)
    (fun x => (f x)^2) (by
      intro x
      dsimp only
      unfold FiniteKernel.eventIndicator
      split_ifs with hx
      · simpa only [mul_one] using (le_of_lt hx)
      · simpa only [mul_zero] using sq_nonneg (f x))
  rwa [finiteLaw_expect_const_mul] at h

theorem weighted_transfer_concentration (L M : ℕ) (hL : 2 ≤ L) (hM : M ≤ L)
    (w : Fin L → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w)) :
    (uniformTransferLaw L M hM).expect (FiniteKernel.eventIndicator (weightedTransferBad L M hM w ε)) ≤
      1/(ε^2*(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w)) := by
  let μ := uniformTransferLaw L M hM
  let m := μ.expect (weightedSubsetTotal L M w)
  have hv := weighted_subset_variance_bound L M hL hM w hw
  have hb := finiteLaw_squared_markov μ (fun S => weightedSubsetTotal L M w S-m) ((ε*m)^2)
  have h := hb.trans hv
  let p := μ.expect (FiniteKernel.eventIndicator (weightedTransferBad L M hM w ε))
  change (ε*m)^2*p ≤ m at h
  change p ≤ 1/(ε^2*m)
  have hden : 0 < ε^2*m := by positivity
  apply (le_div_iff₀ hden).mpr
  have hscale : m*(p*(ε^2*m)) ≤ m*1 := by nlinarith only [h]
  exact (mul_le_mul_iff_right₀ hm).mp hscale

theorem weighted_transfer_good_interval (L M : ℕ) (hM : M ≤ L) (w : Fin L → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hm : 0 ≤ (uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w))
    (S : TransferSubset L M) (hgood : S ∉ weightedTransferBad L M hM w ε) :
    (1-ε)*(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w) ≤ weightedSubsetTotal L M w S ∧
      weightedSubsetTotal L M w S ≤ (1+ε)*(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w) := by
  change ¬ (ε*(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w))^2 <
    (weightedSubsetTotal L M w S-(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w))^2 at hgood
  have hs := le_of_not_gt hgood
  have hb := (sq_le_sq).mp hs
  rw [abs_of_nonneg (mul_nonneg hε hm)] at hb
  have h := abs_le.mp hb
  constructor <;> nlinarith only [h.1,h.2]

end SerialTransferSelection
