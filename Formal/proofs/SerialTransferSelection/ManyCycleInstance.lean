import proofs.SerialTransferSelection.ManyCycleParameters
import proofs.SerialTransferSelection.ManyCycleMeasured

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- Explicit sufficient contract, with all source, clock and founder existence discharged. -/
theorem manyCycle_instance (N B K : ℕ)
    (hN : 140000000000000000000 ≤ N) (hB : 0 < B)
    (δ confidence : ℝ) (hδ : 0 < δ)
    (herror : ∀ (JB JR : ℕ) (qb qr : ℝ),
      candidateTime*qb/JB < δ → (2*B : ℕ)*(5376*qr/JR) < δ →
      historyBudget (fun j => sourceCycleError N (2*B) JB JR qb qr
        candidateTime (baselineFloor j) (1/50)) K 0 < 1-confidence) :
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
  have hfloor (b : Bool) : baselineFloor 0*((2*B : ℕ) : ℝ) ≤ ancestralCount b s.val.live := by
    rw [hcounts b]
    simp [baselineFloor]
  have hpos (b : Bool) : 0 < ancestralCount b s.val.live := by rw [hcounts b]; exact hB
  have hprob := sourceManyCycleLaw_probability N (2*B) JB JR (by omega) (by omega)
    zL zH hzL hzH qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
    qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb hsL hsH
    (by exact_mod_cast hN) (by omega) hJB hJR (by norm_num [candidateGamma])
    (by norm_num [candidateGamma]) hkr hkb
    (by change candidateTime=8/candidateGamma; norm_num [candidateTime,candidateGamma])
    baselineFloor (1/50) baselineFloor_pos (by norm_num) (by norm_num)
    (fun j => (baselineFloor_next j).le) K s hfloor
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
      {h | historyGood (manyCycleStep N (2*B) zL zH baselineFloor (1/50)) K 0 (some s) h}
      (manyMeasuredEvent N (2*B) zL zH (1/50) K s.val)
      (fun h hh => manyCycle_good_measured N (2*B) (by omega) zL zH hzL hzH
        baselineFloor (1/50) K s hnew hpos h hh)
    apply le_trans _ (hprob.trans hmono)
    change confidence ≤ 1-historyBudget (fun j => sourceCycleError N (2*B) JB JR
      qb qr candidateTime (baselineFloor j) (1/50)) K 0
    linarith only [herr]

theorem tenCycle_instance :
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel tenCycleN zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation tenCycleN (2*50000000000000000000) zL zH) x,
          (cycleBatchModel tenCycleN (2*50000000000000000000) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation tenCycleN (2*50000000000000000000) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < (1/10000 : ℝ) ∧
        ((2*50000000000000000000 : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < (1/10000 : ℝ) ∧
        (∀ b, chemicalCount b s.val.live=50000000000000000000) ∧
        (∀ c ∈ s.val.live, c.compartment.2=tenCycleN) ∧
        (99/100 : ℝ) ≤
          (sourceManyCycleLaw tenCycleN (2*50000000000000000000) JB JR (by norm_num [tenCycleN]) (by norm_num [tenCycleN]) zL zH hzL hzH
            qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
            qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb 10 s).expect
            (FiniteKernel.eventIndicator (manyMeasuredEvent tenCycleN (2*50000000000000000000) zL zH (1/50) 10 s.val)) :=
  manyCycle_instance tenCycleN 50000000000000000000 10
    (by norm_num [tenCycleN]) (by norm_num) (1/10000) (99/100) (by norm_num)
    (by
      intro JB JR qb qr hb hr
      have h := tenCycle_error_bound JB JR qb qr hb hr
      norm_num [tenCycleM] at h ⊢
      exact h)

end SerialTransferSelection
