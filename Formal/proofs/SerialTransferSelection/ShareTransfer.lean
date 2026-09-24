import proofs.SerialTransferSelection.ShareGeometry

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

noncomputable def ancestralShare (b : Bool) (s : PopulationState) : ℝ :=
  (ancestralMembrane b s.live : ℝ)/(membrane s.live : ℝ)

theorem transferAncestralMean_share (N M : ℕ) (hN : 0 < N) (s : PopulationState)
    (hL : 0 < s.live.length) (hM : M ≤ s.live.length) (hv : ValidVolumes N s)
    (b : Bool) : (M : ℝ)/2*ancestralShare b s ≤ transferAncestralMean N M b s hM := by
  rw [transferAncestralMean_formula N M b s hL hM]
  apply weighted_mean_share_floor
  · exact_mod_cast hN
  · exact Nat.cast_nonneg M
  · exact_mod_cast hL
  · exact Nat.cast_nonneg _
  · have h := membrane_lower N s.live (fun c hc => (hv c hc).1)
    have hr : (N : ℝ)*(s.live.length : ℝ) ≤ membrane s.live := by exact_mod_cast h
    simpa only [mul_comm] using hr

/-- Sharper second-moment bound on the unchanged uniform intact-cell subset law. -/
theorem source_transfer_share_probability (N M : ℕ) (hN : 0 < N) (hMpos : 0 < M)
    (s : PopulationState) (hL : 2 ≤ s.live.length) (hM : M ≤ s.live.length)
    (hv : ValidVolumes N s) (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε)
    (hshare : ∀ b, q/4 ≤ ancestralShare b s) :
    1-16/(ε^2*(M : ℝ)*q) ≤
      (uniformTransferLaw s.live.length M hM).expect
        (FiniteKernel.eventIndicator (ancestralTransferGoodSet N M s hM ε)) := by
  classical
  let μ := uniformTransferLaw s.live.length M hM
  let bad (b : Bool) := weightedTransferBad s.live.length M hM
    (fun i => ancestralWeight N b (selectedCell s i)) ε
  let δ := 1/(ε^2*((M : ℝ)*q/8))
  have hb (b : Bool) : μ.expect (FiniteKernel.eventIndicator (bad b)) ≤ δ := by
    have hh := transferAncestralMean_share N M hN s (by omega) hM hv b
    have hqmean := mul_le_mul_of_nonneg_left (hshare b) (by positivity : 0 ≤ (M : ℝ)/2)
    have hmean : (M : ℝ)*q/8 ≤ transferAncestralMean N M b s hM := by linarith
    have hmeanpos : 0 < transferAncestralMean N M b s hM :=
      (by positivity : 0 < (M : ℝ)*q/8).trans_le hmean
    have hc := weighted_transfer_concentration s.live.length M hL hM
      (fun i => ancestralWeight N b (selectedCell s i))
      (fun i => ancestralWeight_bounds N hN b (selectedCell s i) ((hv _ (selected_mem s i)).2.le))
      ε hε hmeanpos
    exact hc.trans (one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hmean (sq_nonneg ε)))
  have h := finiteLaw_two_complements μ (bad true) (bad false)
  have heq : (bad true)ᶜ ∩ (bad false)ᶜ=ancestralTransferGoodSet N M s hM ε := by
    ext S
    simp [ancestralTransferGoodSet,bad,Bool.forall_bool,and_comm]
  rw [heq] at h
  have hδ : δ+δ=16/(ε^2*(M : ℝ)*q) := by
    dsimp [δ]
    field_simp
    ring
  linarith only [h,hb true,hb false,hδ]

end SerialTransferSelection
