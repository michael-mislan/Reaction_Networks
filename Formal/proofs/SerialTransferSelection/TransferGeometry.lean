import proofs.SerialTransferSelection.TransferMean

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem relative_log_odds_lower (a b x y ε : ℝ) (ha : 0 < a) (hb : 0 < b)
    (_hx : 0 < x) (hy : 0 < y) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hl : (1-ε)*a ≤ x) (hu : y ≤ (1+ε)*b) :
    Real.log a-Real.log b-Real.log ((1+ε)/(1-ε)) ≤ Real.log x-Real.log y := by
  have hm : 0 < 1-ε := by linarith
  have hp : 0 < 1+ε := by linarith
  have hlow := Real.log_le_log (mul_pos hm ha) hl
  have hhigh := Real.log_le_log hy hu
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt ha)] at hlow
  rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hb)] at hhigh
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
  linarith only [hlow,hhigh]

theorem transfer_ancestral_interval (N M : ℕ) (hN : 0 < N) (tag : Bool) (s : PopulationState)
    (hL : 0 < s.live.length) (hM : M ≤ s.live.length) (ε : ℝ) (hε : 0 ≤ ε)
    (S : TransferSubset s.live.length M)
    (hgood : S ∉ weightedTransferBad s.live.length M hM
      (fun i => ancestralWeight N tag (selectedCell s i)) ε) :
    (1-ε)*((M : ℝ)/(s.live.length : ℝ))*(ancestralMembrane tag s.live : ℝ) ≤
      (ancestralMembrane tag (exchangeSelectedMedium M s S).live : ℝ) ∧
    (ancestralMembrane tag (exchangeSelectedMedium M s S).live : ℝ) ≤
      (1+ε)*((M : ℝ)/(s.live.length : ℝ))*(ancestralMembrane tag s.live : ℝ) := by
  have hmean : 0 ≤ transferAncestralMean N M tag s hM := by
    rw [transferAncestralMean_formula N M tag s hL hM]
    positivity
  have h := weighted_transfer_good_interval s.live.length M hM
    (fun i => ancestralWeight N tag (selectedCell s i)) ε hε hmean S hgood
  rw [selected_weight_membrane] at h
  change (1-ε)*transferAncestralMean N M tag s hM ≤ _ ∧
    _ ≤ (1+ε)*transferAncestralMean N M tag s hM at h
  rw [transferAncestralMean_formula N M tag s hL hM] at h
  have hden : 0 < 2*(N : ℝ) := by positivity
  have hl := (le_div_iff₀ hden).mp h.1
  have hu := (div_le_iff₀ hden).mp h.2
  constructor
  · simpa only [mul_assoc,div_mul_cancel₀ _ (ne_of_gt hden)] using hl
  · simpa only [mul_assoc,div_mul_cancel₀ _ (ne_of_gt hden)] using hu

theorem transfer_size_odds_loss (N M : ℕ) (hN : 0 < N) (hMpos : 0 < M) (s : PopulationState)
    (hL : 0 < s.live.length) (hM : M ≤ s.live.length) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hH : 0 < ancestralMembrane true s.live) (hLo : 0 < ancestralMembrane false s.live)
    (S : TransferSubset s.live.length M)
    (hg : ∀ tag, S ∉ weightedTransferBad s.live.length M hM
      (fun i => ancestralWeight N tag (selectedCell s i)) ε) :
    Real.log (ancestralMembrane true s.live)-Real.log (ancestralMembrane false s.live)-
      Real.log ((1+ε)/(1-ε)) ≤
      Real.log (ancestralMembrane true (exchangeSelectedMedium M s S).live)-
      Real.log (ancestralMembrane false (exchangeSelectedMedium M s S).live) := by
  have hh := transfer_ancestral_interval N M hN true s hL hM ε hε S (hg true)
  have hl := transfer_ancestral_interval N M hN false s hL hM ε hε S (hg false)
  let c := (M : ℝ)/(s.live.length : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : 0 < 1-ε := by linarith
  have hHreal : 0 < (ancestralMembrane true s.live : ℝ) := by exact_mod_cast hH
  have hLreal : 0 < (ancestralMembrane false s.live : ℝ) := by exact_mod_cast hLo
  have hx : 0 < (ancestralMembrane true (exchangeSelectedMedium M s S).live : ℝ) :=
    (mul_pos (mul_pos hm hc) hHreal).trans_le hh.1
  have hy : 0 < (ancestralMembrane false (exchangeSelectedMedium M s S).live : ℝ) :=
    (mul_pos (mul_pos hm hc) hLreal).trans_le hl.1
  have h := relative_log_odds_lower (c*(ancestralMembrane true s.live : ℝ))
    (c*(ancestralMembrane false s.live : ℝ)) _ _ ε (mul_pos hc hHreal) (mul_pos hc hLreal)
    hx hy hε hε1 (by simpa only [mul_assoc] using hh.1) (by simpa only [mul_assoc] using hl.2)
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hHreal),Real.log_mul (ne_of_gt hc) (ne_of_gt hLreal)] at h
  linarith only [h]

end SerialTransferSelection
