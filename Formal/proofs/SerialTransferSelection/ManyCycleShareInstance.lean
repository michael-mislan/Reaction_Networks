import proofs.SerialTransferSelection.ManyCycleParameters
import proofs.SerialTransferSelection.ManyCycleShare
import proofs.SerialTransferSelection.ShareParameters

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- Explicit sufficient contract, with all source, clock and founder existence discharged. -/
theorem manyCycle_share_instance (N B K : ℕ)
    (hN : 140000000000000000000 ≤ N) (hB : 0 < B)
    (δ confidence : ℝ) (hδ : 0 < δ)
    (herror : ∀ (JB JR : ℕ) (qb qr : ℝ),
      candidateTime*qb/JB < δ → (2*B : ℕ)*(5376*qr/JR) < δ →
      historyBudget (fun j => shareCycleError N (2*B) JB JR qb qr
        candidateTime (shareFloor j) (1/50)) K 0 < 1-confidence) :
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
        confidence ≤
          (sourceManyCycleLaw N (2*B) JB JR (by omega) (by omega) zL zH hzL hzH
            qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
            qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb K s).expect
            (FiniteKernel.eventIndicator (manyMeasuredEvent N (2*B) zL zH (1/50) K s.val)) := by
  obtain ⟨zL,hzL,hsL⟩ := low_source_root
  obtain ⟨zH,hzH,hsH⟩ := high_source_root
  obtain ⟨qb,qr,hqb,hqr,hkb,hkr,hclockb,hclockr⟩ := exists_uniform_source_clocks N (2*B)
    zL zH candidateGamma (by norm_num [candidateGamma])
    ((9/40000)*(N : ℝ)*candidateGamma) ((N : ℝ)*localAlpha*innerEnergy/672)
  obtain ⟨JB,JR,hJB,hJR,hb,hr⟩ := exists_uniform_cycle_quotas (2*B) (by omega)
    qb qr candidateTime δ hδ
  obtain ⟨s,hcounts,hnew⟩ := balanced_initial_newborn N B (by omega) zL zH hzL hzH
  have hfloor (b : Bool) : shareFloor 0 ≤ ancestralShare b s.val := by
    have ha (b : Bool) : ancestralMembrane b s.val.live=N*B := by
      rw [newborn_ancestral_size N s.val.live hnew b,hcounts b]
    unfold ancestralShare
    rw [ha b,← ancestral_membrane_total s.val.live,ha true,ha false]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
    norm_num [shareFloor]
    field_simp
    nlinarith
  have hpos (b : Bool) : 0 < ancestralCount b s.val.live := by rw [hcounts b]; exact hB
  have hprob := sourceManyCycleLaw_share_probability N (2*B) JB JR (by omega) (by omega)
    zL zH hzL hzH qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
    qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb hsL hsH
    (by exact_mod_cast hN) (by omega) hJB hJR (by norm_num [candidateGamma])
    (by norm_num [candidateGamma]) hkr hkb
    (by change candidateTime=8/candidateGamma; norm_num [candidateTime,candidateGamma])
    shareFloor (1/50) shareFloor_pos (by norm_num) (by norm_num)
    (fun j => (shareFloor_next j).le) K s hfloor
  have herr := herror JB JR qb qr hb hr
  refine ⟨zL,zH,hzL,hzH,hsL,hsH,JB,JR,qb,qr,hqb,hqr,hclockr,hclockb,s,
    hJB,hJR,hb,hr,?_,hnew,?_⟩
  · intro b
    rw [chemicalCount_eq_ancestralCount b s.val.live
      (fun c hc => ready_population_readout N (2*B) zL zH hzL hzH s c hc)]
    exact hcounts b
  · have hmono := finiteLaw_event_mono_many
      (sourceManyCycleLaw N (2*B) JB JR (by omega) (by omega) zL zH hzL hzH
        qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
        qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb K s)
      {h | historyGood (shareHistoryStep N (2*B) zL zH shareFloor (1/50)) K 0 (some s) h}
      (manyMeasuredEvent N (2*B) zL zH (1/50) K s.val)
      (fun h hh => shareHistory_measured N (2*B) (by omega) zL zH hzL hzH
        shareFloor (1/50) K s hnew hpos h hh)
    apply le_trans _ (hprob.trans hmono)
    change confidence ≤ 1-historyBudget (fun j => shareCycleError N (2*B) JB JR
      qb qr candidateTime (shareFloor j) (1/50)) K 0
    linarith only [herr]


theorem refined_tenCycle_instance :
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel tenCycleN zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation tenCycleN (2*500000000000000) zL zH) x,
          (cycleBatchModel tenCycleN (2*500000000000000) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation tenCycleN (2*500000000000000) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < (1/10000 : ℝ) ∧
        ((2*500000000000000 : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < (1/10000 : ℝ) ∧
        (∀ b, chemicalCount b s.val.live=500000000000000) ∧
        (∀ c ∈ s.val.live, c.compartment.2=tenCycleN) ∧
        (99/100 : ℝ) ≤
          (sourceManyCycleLaw tenCycleN (2*500000000000000) JB JR (by norm_num [tenCycleN]) (by norm_num [tenCycleN]) zL zH hzL hzH
            qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
            qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb 10 s).expect
            (FiniteKernel.eventIndicator (manyMeasuredEvent tenCycleN (2*500000000000000) zL zH (1/50) 10 s.val)) :=
  manyCycle_share_instance tenCycleN 500000000000000 10
    (by norm_num [tenCycleN]) (by norm_num) (1/10000) (99/100) (by norm_num)
    (by
      intro JB JR qb qr hb hr
      have h := refined_tenCycle_error JB JR qb qr hb hr
      norm_num [refinedM] at h ⊢
      exact h)

end SerialTransferSelection
