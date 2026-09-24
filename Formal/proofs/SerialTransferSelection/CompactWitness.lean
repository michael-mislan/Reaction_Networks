import proofs.SerialTransferSelection.ManyCycleShareInstance

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def compactN : ℕ := 65536000000000000000000
def compactM : ℕ := 10000000000000

theorem compact_chemical_bound : chemicalCycleError compactN compactM candidateTime ≤ 11/10^7 := by
  have h (x : ℝ) (hx : 128 ≤ x) : Real.exp (-x) ≤ 1/(2 : ℝ)^128 :=
    (exp_negative_integer_bound 128 x hx).trans (by norm_num)
  have h1 := h 896 (by norm_num)
  have h2 := h 512 (by norm_num)
  have h3 := h 960 (by norm_num)
  have h4 := h 128 (by norm_num)
  have h5 := h 192 (by norm_num)
  have h6 := h ((compactN : ℝ)/(35*10^12)) (by norm_num [compactN])
  have h7 := h ((compactN : ℝ)/2500) (by norm_num [compactN])
  have h8 := h (19*(compactN : ℝ)/500000) (by norm_num [compactN])
  have h9 := exp_negative_integer_bound 64 64 (by norm_num)
  have h10 := h 1024 (by norm_num)
  have h11 := h 1984 (by norm_num)
  unfold chemicalCycleError
  rw [phaseChemicalRawError_expanded]
  norm_num [compactN,compactM,candidateTime,localAlpha,innerEnergy,outerEnergy,
    partitionError,recoveryError] at h6 h7 h8 ⊢
  linarith only [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

theorem compact_transfer_bound :
    80000/(compactM : ℝ)*historyBudget (fun j => (204/49 : ℝ)^j) 10 0 < 396/100000 := by
  norm_num [historyBudget,compactM]

theorem compact_tenCycle_error (JB JR : ℕ) (qb qr : ℝ)
    (hb : candidateTime*qb/JB < 1/10000)
    (hr : (compactM : ℝ)*(5376*qr/JR) < 1/10000) :
    historyBudget (fun j => shareCycleError compactN compactM JB JR qb qr
      candidateTime (shareFloor j) (1/50)) 10 0 < 1-994/1000 := by
  rw [share_geometric_budget _ _ _ _ _ (by norm_num [compactM])]
  have ht := compact_transfer_bound
  have hc := compact_chemical_bound
  norm_num only [Nat.cast_ofNat]
  linarith

theorem compact_tenCycle_instance :
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel compactN zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation compactN (2*5000000000000) zL zH) x,
          (cycleBatchModel compactN (2*5000000000000) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation compactN (2*5000000000000) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < (1/10000 : ℝ) ∧
        ((2*5000000000000 : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < (1/10000 : ℝ) ∧
        (∀ b, chemicalCount b s.val.live=5000000000000) ∧
        (∀ c ∈ s.val.live, c.compartment.2=compactN) ∧
        (994/1000 : ℝ) ≤
          (sourceManyCycleLaw compactN (2*5000000000000) JB JR (by norm_num [compactN]) (by norm_num [compactN]) zL zH hzL hzH
            qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
            qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb 10 s).expect
            (FiniteKernel.eventIndicator (manyMeasuredEvent compactN (2*5000000000000) zL zH (1/50) 10 s.val)) :=
  manyCycle_share_instance compactN 5000000000000 10
    (by norm_num [compactN]) (by norm_num) (1/10000) (994/1000) (by norm_num)
    (by
      intro JB JR qb qr hb hr
      have h := compact_tenCycle_error JB JR qb qr hb hr
      norm_num [compactM] at h ⊢
      exact h)

end SerialTransferSelection
