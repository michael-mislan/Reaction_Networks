import proofs.SerialTransferSelection.TransferGeometry

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem transfer_count_frequency_floor (N M : ℕ) (hN : 0 < N) (hMpos : 0 < M)
    (tag : Bool) (s : PopulationState) (hL : 0 < s.live.length) (hM : M ≤ s.live.length)
    (hcap : s.live.length ≤ 8*M) (hv : ValidVolumes N s)
    (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hB : (N : ℝ)*p*M ≤ ancestralMembrane tag s.live)
    (S : TransferSubset s.live.length M)
    (hgood : S ∉ weightedTransferBad s.live.length M hM
      (fun i => ancestralWeight N tag (selectedCell s i)) ε) :
    0 < ancestralCount tag (exchangeSelectedMedium M s S).live ∧
      (1-ε)*p/16 ≤ (ancestralCount tag (exchangeSelectedMedium M s S).live : ℝ)/(M : ℝ) := by
  have hmean := transferAncestralMean_floor N M hN tag s hL hM hcap p hp.le hB
  have hmeanpos : 0 < transferAncestralMean N M tag s hM :=
    (by positivity : 0 < p*(M : ℝ)/16).trans_le hmean
  have hi := weighted_transfer_good_interval s.live.length M hM
    (fun i => ancestralWeight N tag (selectedCell s i)) ε hε hmeanpos.le S hgood
  have hvol (c : TaggedCell) (hc : c ∈ (exchangeSelectedMedium M s S).live) :
      N ≤ c.compartment.2 ∧ c.compartment.2 ≤ 2*N :=
    ⟨(hv c (exchangeSelectedMedium_preserves M s S c hc)).1,
      (hv c (exchangeSelectedMedium_preserves M s S c hc)).2.le⟩
  have hcount := (ancestral_count_bounds N tag (exchangeSelectedMedium M s S).live hvol).2
  have hcountR : (ancestralMembrane tag (exchangeSelectedMedium M s S).live : ℝ) ≤
      2*(N : ℝ)*(ancestralCount tag (exchangeSelectedMedium M s S).live : ℝ) := by exact_mod_cast hcount
  have hnormalized : weightedSubsetTotal s.live.length M
      (fun i => ancestralWeight N tag (selectedCell s i)) S ≤
      (ancestralCount tag (exchangeSelectedMedium M s S).live : ℝ) := by
    rw [selected_weight_membrane]
    apply (div_le_iff₀ (by positivity : 0 < 2*(N : ℝ))).mpr
    nlinarith only [hcountR]
  have hm : 0 < 1-ε := by linarith
  have hf := mul_le_mul_of_nonneg_left hmean hm.le
  have htotal : (1-ε)*p*(M : ℝ)/16 ≤ (ancestralCount tag (exchangeSelectedMedium M s S).live : ℝ) := by
    change (1-ε)*transferAncestralMean N M tag s hM ≤ _ ∧ _ at hi
    nlinarith only [hf,hi.1,hnormalized]
  constructor
  · have hpos := (by positivity : 0 < (1-ε)*p*(M : ℝ)/16).trans_le htotal
    exact_mod_cast hpos
  · apply (le_div_iff₀ (by positivity : 0 < (M : ℝ))).mpr
    nlinarith only [htotal]

end SerialTransferSelection
