import proofs.SerialTransferSelection.TransferPhysical

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem weightedSubsetTotal_mean_scaled (L M : ℕ) (hM : M ≤ L) (w : Fin L → ℝ) :
    (L : ℝ)*(uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w)=
      (M : ℝ)*(∑ i, w i) := by
  rw [weightedSubsetTotal_mean,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc,subset_marginal_total]

theorem weightedSubsetTotal_mean_formula (L M : ℕ) (hL : 0 < L) (hM : M ≤ L) (w : Fin L → ℝ) :
    (uniformTransferLaw L M hM).expect (weightedSubsetTotal L M w)=
      ((M : ℝ)/(L : ℝ))*(∑ i, w i) := by
  have h := weightedSubsetTotal_mean_scaled L M hM w
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hL0)
  calc
    _ = (M : ℝ)*(∑ i, w i) := h
    _ = _ := by field_simp

noncomputable def transferAncestralMean (N M : ℕ) (tag : Bool) (s : PopulationState)
    (hM : M ≤ s.live.length) : ℝ :=
  (uniformTransferLaw s.live.length M hM).expect
    (weightedSubsetTotal s.live.length M (fun i => ancestralWeight N tag (selectedCell s i)))

theorem transferAncestralMean_formula (N M : ℕ) (tag : Bool) (s : PopulationState)
    (hL : 0 < s.live.length) (hM : M ≤ s.live.length) :
    transferAncestralMean N M tag s hM=
      ((M : ℝ)/(s.live.length : ℝ))*((ancestralMembrane tag s.live : ℝ)/(2*(N : ℝ))) := by
  unfold transferAncestralMean
  rw [weightedSubsetTotal_mean_formula _ _ hL,full_weight_membrane]

theorem transferAncestralMean_floor (N M : ℕ) (hN : 0 < N) (tag : Bool) (s : PopulationState)
    (hL : 0 < s.live.length) (hM : M ≤ s.live.length) (hcap : s.live.length ≤ 8*M)
    (p : ℝ) (hp : 0 ≤ p) (hB : (N : ℝ)*p*M ≤ ancestralMembrane tag s.live) :
    p*(M : ℝ)/16 ≤ transferAncestralMean N M tag s hM := by
  have hLpos : 0 < (s.live.length : ℝ) := by exact_mod_cast hL
  have hNpos : 0 < 2*(N : ℝ) := by positivity
  have hcapR : (s.live.length : ℝ) ≤ 8*(M : ℝ) := by exact_mod_cast hcap
  have hratio : (1/8 : ℝ) ≤ (M : ℝ)/(s.live.length : ℝ) := by
    apply (le_div_iff₀ hLpos).mpr
    nlinarith only [hcapR]
  have hnorm : p*(M : ℝ)/2 ≤ (ancestralMembrane tag s.live : ℝ)/(2*(N : ℝ)) := by
    apply (le_div_iff₀ hNpos).mpr
    nlinarith only [hB]
  rw [transferAncestralMean_formula N M tag s hL hM]
  have h := mul_le_mul hratio hnorm (by positivity : 0 ≤ p*(M : ℝ)/2) (by positivity)
  nlinarith only [h]

end SerialTransferSelection
