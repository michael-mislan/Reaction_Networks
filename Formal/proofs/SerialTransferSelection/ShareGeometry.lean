import proofs.SerialTransferSelection.TransferJointProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- Conservation and the two weighted transfer intervals imply a share recurrence. -/
theorem share_transfer_recurrence (B W Bpre Wpre Bpost Wpost r ε : ℝ)
    (hB : 0 ≤ B) (hW : 0 < W) (hpost : 0 < Wpost) (hr : 0 < r)
    (he : 0 ≤ ε) (he1 : ε < 1) (hcons : Wpre=4*W) (hgrow : B ≤ Bpre)
    (hl : (1-ε)*r*Bpre ≤ Bpost) (hu : Wpost ≤ (1+ε)*r*Wpre) :
    (1-ε)/(4*(1+ε))*(B/W) ≤ Bpost/Wpost := by
  have hm : 0 < 1-ε := by linarith
  have hp : 0 < 1+ε := by linarith
  have hBpre : 0 ≤ Bpre := hB.trans hgrow
  have hbpost : 0 ≤ Bpost := (by positivity : 0 ≤ (1-ε)*r*Bpre).trans hl
  have hc : 0 < (1+ε)*r*(4*W) := by positivity
  have hlow : (1-ε)*r*B ≤ Bpost :=
    (mul_le_mul_of_nonneg_left hgrow (by positivity)).trans hl
  rw [hcons] at hu
  have hdiv := div_le_div₀ hbpost (le_refl Bpost) hpost hu
  have hratio : ((1-ε)*r*B)/((1+ε)*r*(4*W)) ≤ Bpost/((1+ε)*r*(4*W)) :=
    div_le_div_of_nonneg_right hlow hc.le
  have hid : (1-ε)/(4*(1+ε))*(B/W) = ((1-ε)*r*B)/((1+ε)*r*(4*W)) := by
    field_simp
  rw [hid]
  exact hratio.trans hdiv

theorem count_share_conversion (B W C N M : ℝ) (hB : 0 ≤ B) (hN : 0 < N)
    (hM : 0 < M) (hW : N*M ≤ W) (hC : B ≤ 2*N*C) :
    (B/W)/2 ≤ C/M := by
  have hw : 0 < W := (mul_pos hN hM).trans_le hW
  have hc : 0 ≤ C := by nlinarith
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity : 0 < W*2) hM).mpr
  have h1 := mul_le_mul_of_nonneg_right hC hM.le
  have h2 := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 2*C)
  nlinarith only [h1,h2]

theorem weighted_mean_share_floor (N M n B W : ℝ)
    (hN : 0 < N) (hM : 0 ≤ M) (hn : 0 < n) (hB : 0 ≤ B)
    (hW : n*N ≤ W) : M/2*(B/W) ≤ (M/n)*(B/(2*N)) := by
  have hw : 0 < W := (mul_pos hn hN).trans_le hW
  have hbound : B/W ≤ B/(n*N) := div_le_div₀ hB le_rfl (mul_pos hn hN) hW
  have h := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ M/2)
  convert h using 1
  field_simp

end SerialTransferSelection
