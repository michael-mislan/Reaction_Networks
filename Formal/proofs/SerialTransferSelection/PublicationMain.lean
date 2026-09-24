import proofs.SerialTransferSelection.ImprovedInstance
import proofs.SerialTransferSelection.OperationalCorollaries
import proofs.SerialTransferSelection.ProtocolCertificate
import proofs.SerialTransferSelection.AnalyticClocks

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem original_newborn_instance :
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel candidateN zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation candidateN (2*500000000000000) zL zH) x,
          (cycleBatchModel candidateN (2*500000000000000) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation candidateN (2*500000000000000) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < 1/1000 ∧
        ((2*500000000000000 : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < 1/1000 ∧
        (∀ b, chemicalCount b s.val.live=500000000000000) ∧
        (∀ c ∈ s.val.live, c.compartment.2=candidateN) ∧
        (∀ c ∈ s.val.live, chemicalReadout c=c.high) ∧
        (497999/500000 : ℝ) ≤
          (sourceTwoCycleLaw candidateN (2*500000000000000) JB JR (by norm_num [candidateN])
            (by norm_num [candidateN]) zL zH hzL hzH qr hqr hclockr candidateGamma
            (by norm_num [candidateGamma]) qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb s).expect
            (FiniteKernel.eventIndicator (successfulOutput (newbornMeasuredGain candidateN (2*500000000000000) zL zH s.val))) := by
  apply improved_serial_instance candidateN 500000000000000 (by norm_num [candidateN]) (by norm_num) (497999/500000)
  intro JB JR qb qr hb hr
  have h := original_sharp_error JB JR qb qr hb hr
  norm_num at h ⊢
  exact h

theorem smaller_newborn_instance :
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel smallerN zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation smallerN (2*2000000000) zL zH) x,
          (cycleBatchModel smallerN (2*2000000000) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation smallerN (2*2000000000) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < 1/1000 ∧
        ((2*2000000000 : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < 1/1000 ∧
        (∀ b, chemicalCount b s.val.live=2000000000) ∧
        (∀ c ∈ s.val.live, c.compartment.2=smallerN) ∧
        (∀ c ∈ s.val.live, chemicalReadout c=c.high) ∧
        (495999/500000 : ℝ) ≤
          (sourceTwoCycleLaw smallerN (2*2000000000) JB JR (by norm_num [smallerN])
            (by norm_num [smallerN]) zL zH hzL hzH qr hqr hclockr candidateGamma
            (by norm_num [candidateGamma]) qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb s).expect
            (FiniteKernel.eventIndicator (successfulOutput (newbornMeasuredGain smallerN (2*2000000000) zL zH s.val))) := by
  apply improved_serial_instance smallerN 2000000000 (by norm_num [smallerN]) (by norm_num) (495999/500000)
  intro JB JR qb qr hb hr
  have h := smaller_sharp_error JB JR qb qr hb hr
  norm_num at h ⊢
  exact h

end SerialTransferSelection
