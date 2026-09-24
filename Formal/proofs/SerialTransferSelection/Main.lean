import proofs.SerialTransferSelection.MeasuredCounts
import proofs.SerialTransferSelection.ProtocolCertificate

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- ROOT-C3: a realized finite source instance with type-neutral physical operations,
finite maintained-service allowances, and at least99% probability of strictly
positive retained chemical cell-count enrichment across two eligible cycles.
The finite stopped/marked law and its failure quotient are explicit in the conclusion. -/
theorem source_serial_transfer_c3 :
    SerialProtocolCertificate ∧
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel candidateN zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation candidateN candidateM zL zH) x,
          (cycleBatchModel candidateN candidateM zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation candidateN candidateM zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < 1/1000 ∧
        (candidateM : ℝ)*(5376*(qr : ℝ)/JR) < 1/1000 ∧
        (∀ b, chemicalCount b s.val.live=500000000000000) ∧
        (∀ c ∈ s.val.live, chemicalReadout c=c.high) ∧
        (99/100 : ℝ) ≤
          (sourceTwoCycleLaw candidateN candidateM JB JR (by norm_num [candidateN])
            (by norm_num [candidateM]) zL zH hzL hzH qr hqr hclockr candidateGamma
            (by norm_num [candidateGamma]) qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb s).expect
            (FiniteKernel.eventIndicator (successfulOutput (measuredCountGain candidateN candidateM zL zH s.val))) := by
  refine ⟨serial_protocol_certified,?_⟩
  obtain ⟨zL,zH,hzL,hzH,hsL,hsH,JB,JR,qb,qr,hqb,hqr,hclockr,hclockb,s,
    hJB,hJR,hb,hr,hcounts,hread,hprob⟩ := nonvacuous_serial_count_instance
  refine ⟨zL,zH,hzL,hzH,hsL,hsH,JB,JR,qb,qr,hqb,hqr,hclockr,hclockb,s,
    hJB,hJR,hb,hr,?_,hread,?_⟩
  · intro b
    rw [chemicalCount_eq_ancestralCount b s.val.live hread]
    exact hcounts b
  · apply hprob.trans
    apply finiteLaw_successful_mono
    intro y hy
    exact realized_gain_is_measured candidateN candidateM zL zH s.val hread y hy

end SerialTransferSelection
