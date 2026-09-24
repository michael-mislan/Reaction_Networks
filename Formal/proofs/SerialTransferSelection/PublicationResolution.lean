import proofs.SerialTransferSelection.EnrichmentDesign
import proofs.SerialTransferSelection.SourceHorizonDesign
import proofs.SerialTransferSelection.StrongShareInstance
import proofs.SerialTransferSelection.ManyCycleAccounts
import proofs.SerialTransferSelection.TransferLossBounds

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem publication_tenCycle_instance :
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
            (FiniteKernel.eventIndicator {h | manyMeasuredEvent compactN (2*5000000000000) zL zH (1/50) 10 s.val h ∧ historyGood (shareHistoryStep compactN (2*5000000000000) zL zH shareFloor (1/50)) 10 0 (some s) h}) :=
  strong_manyCycle_share_instance compactN 5000000000000 10
    (by norm_num [compactN]) (by norm_num) (1/10000) (994/1000) (by norm_num)
    (by
      intro JB JR qb qr hb hr
      have h := compact_tenCycle_error JB JR qb qr hb hr
      norm_num [compactM] at h ⊢
      exact h)

theorem publication_terminal_interpretation (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : ReadyPopulation compactN compactM zL zH)
    (hbalanced : ∀ b, chemicalCount b s.val.live=5000000000000)
    (h : Fin 10 → Option (ReadyPopulation compactN compactM zL zH))
    (hh : manyMeasuredEvent compactN compactM zL zH (1/50) 10 s.val h ∧
      historyGood (shareHistoryStep compactN compactM zL zH shareFloor (1/50)) 10 0 (some s) h) :
    ∃ y : ReadyPopulation compactN compactM zL zH, h ⟨9,by norm_num⟩=some y ∧
      (998935/1000000 : ℝ) < (chemicalCount true y.val.live : ℝ)/(compactM : ℝ) ∧
      1598083 ≤ chemicalCount false y.val.live := by
  obtain ⟨y,hy,hpos,hgain⟩ := hh.1 ⟨9,by norm_num⟩
  obtain ⟨z,hz,hfloor⟩ := share_history_count_floor compactN compactM 10
    (by norm_num [compactN]) (by norm_num [compactM]) zL zH s h hh.2 ⟨9,by norm_num⟩
  have hzy : z=y := Option.some.inj (hz.symm.trans hy)
  subst z
  have hread := fun c hc => ready_population_readout compactN compactM zL zH hzL hzH y c hc
  have heq (b : Bool) := chemicalCount_eq_ancestralCount b y.val.live hread
  have htotal : chemicalCount true y.val.live+chemicalCount false y.val.live=compactM := by
    rw [heq true,heq false,ancestralCount_total]
    exact (readyPopulation_ready compactN compactM zL zH y).1
  have hzero : chemicalCountLogOdds s.val=0 := by
    unfold chemicalCountLogOdds
    rw [hbalanced true,hbalanced false,sub_self]
  rw [hzero,sub_zero] at hgain
  norm_num only [Nat.cast_ofNat] at hgain
  have hf := tenCycle_high_fraction _ _ (by exact_mod_cast hpos true)
    (by exact_mod_cast hpos false) hgain
  have htotalR : (chemicalCount true y.val.live : ℝ)+(chemicalCount false y.val.live : ℝ)=compactM := by
    exact_mod_cast htotal
  rw [htotalR] at hf
  refine ⟨y,hy,hf,compact_minority_integer _ ?_⟩
  rw [heq false]
  simpa using hfloor false

end SerialTransferSelection
