import proofs.SerialTransferSelection.TransferFrequency

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem finiteLaw_two_complements {α : Type*} [Fintype α] (μ : FiniteLaw α) (A B : Set α) :
    1-μ.expect (FiniteKernel.eventIndicator A)-μ.expect (FiniteKernel.eventIndicator B) ≤
      μ.expect (FiniteKernel.eventIndicator (Aᶜ ∩ Bᶜ)) := by
  classical
  have h := μ.expect_mono
    (fun x => 1-FiniteKernel.eventIndicator A x-FiniteKernel.eventIndicator B x)
    (FiniteKernel.eventIndicator (Aᶜ ∩ Bᶜ)) (by
      intro x
      by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
        simp [FiniteKernel.eventIndicator,ha,hb])
  rwa [finiteLaw_expect_sub,finiteLaw_expect_sub,FiniteLaw.expect_const] at h

noncomputable def ancestralTransferGoodSet (N M : ℕ) (s : PopulationState)
    (hM : M ≤ s.live.length) (ε : ℝ) : Set (TransferSubset s.live.length M) :=
  {S | ∀ tag, S ∉ weightedTransferBad s.live.length M hM
    (fun i => ancestralWeight N tag (selectedCell s i)) ε}

theorem source_transfer_weighted_probability (N M : ℕ) (hN : 0 < N) (hMpos : 0 < M)
    (s : PopulationState) (hL : 2 ≤ s.live.length) (hM : M ≤ s.live.length)
    (hcap : s.live.length ≤ 8*M) (hv : ValidVolumes N s)
    (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε)
    (hB : ∀ tag, (N : ℝ)*p*M ≤ ancestralMembrane tag s.live) :
    1-32/(ε^2*p*(M : ℝ)) ≤
      (uniformTransferLaw s.live.length M hM).expect
        (FiniteKernel.eventIndicator (ancestralTransferGoodSet N M s hM ε)) := by
  classical
  let μ := uniformTransferLaw s.live.length M hM
  let bad (tag : Bool) := weightedTransferBad s.live.length M hM
    (fun i => ancestralWeight N tag (selectedCell s i)) ε
  let δ := 1/(ε^2*(p*(M : ℝ)/16))
  have hb (tag : Bool) : μ.expect (FiniteKernel.eventIndicator (bad tag)) ≤ δ := by
    have hmean := transferAncestralMean_floor N M hN tag s (by omega) hM hcap p hp.le (hB tag)
    have hmeanpos : 0 < transferAncestralMean N M tag s hM :=
      (by positivity : 0 < p*(M : ℝ)/16).trans_le hmean
    have hc := weighted_transfer_concentration s.live.length M hL hM
      (fun i => ancestralWeight N tag (selectedCell s i))
      (fun i => ancestralWeight_bounds N hN tag (selectedCell s i) ((hv _ (selected_mem s i)).2.le))
      ε hε hmeanpos
    have hden : 0 < ε^2*(p*(M : ℝ)/16) := by positivity
    have hcomp := mul_le_mul_of_nonneg_left hmean (sq_nonneg ε)
    have hi := one_div_le_one_div_of_le hden hcomp
    exact hc.trans hi
  have h := finiteLaw_two_complements μ (bad true) (bad false)
  have heq : (bad true)ᶜ ∩ (bad false)ᶜ=ancestralTransferGoodSet N M s hM ε := by
    ext S
    simp [ancestralTransferGoodSet,bad,Bool.forall_bool,and_comm]
  rw [heq] at h
  have hδ : δ+δ=32/(ε^2*p*(M : ℝ)) := by
    dsimp [δ]
    field_simp
    ring
  linarith only [h,hb true,hb false,hδ]

end SerialTransferSelection
