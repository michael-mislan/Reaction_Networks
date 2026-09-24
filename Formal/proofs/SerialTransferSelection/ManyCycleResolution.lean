import proofs.SerialTransferSelection.ManyCycleInstance
import proofs.SerialTransferSelection.ManyCycleAvailability
import proofs.SerialTransferSelection.MinorityBoundary
import proofs.SerialTransferSelection.TransferLoss
import proofs.SerialTransferSelection.ShareGeometry
import proofs.SerialTransferSelection.ShareTransfer
import proofs.SerialTransferSelection.EligibleHistory
import proofs.SerialTransferSelection.ShareCycleGeometry
import proofs.SerialTransferSelection.TransferLossBounds
import proofs.SerialTransferSelection.ManyCycleShare
import proofs.SerialTransferSelection.ManyCycleShareInstance
import proofs.SerialTransferSelection.SourceEligibleHistory
import proofs.SerialTransferSelection.NormalizationRefinement
import proofs.SerialTransferSelection.ManyCycleAccounts

/-! Quantified source assembly. The general finite-history bounds, concrete
baseline/refined witnesses, and exact rarity laws are imported above. -/

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem arbitrary_horizon_source_instance (K : ℕ) :
    ∃ (N B : ℕ) (hN : 140000000000000000000 ≤ N) (hB : 0 < B) (δ : ℝ),
      0 < δ ∧
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation N (2*B) zL zH) x,
          (cycleBatchModel N (2*B) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation N (2*B) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < δ ∧
        ((2*B : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < δ ∧
        (∀ b, chemicalCount b s.val.live=B) ∧
        (∀ c ∈ s.val.live, c.compartment.2=N) ∧
        (99/100 : ℝ) ≤
          (sourceManyCycleLaw N (2*B) JB JR (by omega) (by omega) zL zH hzL hzH
            qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
            qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb K s).expect
            (FiniteKernel.eventIndicator (manyMeasuredEvent N (2*B) zL zH (1/50) K s.val)) := by
  obtain ⟨N,B,δ,hN,hB,hδ,herror⟩ := exists_manyCycle_parameters K
  refine ⟨N,B,hN,hB,δ,hδ,?_⟩
  apply manyCycle_instance N B K hN hB δ (99/100) hδ
  intro JB JR qb qr hb hr
  have hh := herror JB JR qb qr hb hr
  norm_num at ⊢
  exact hh

end SerialTransferSelection
