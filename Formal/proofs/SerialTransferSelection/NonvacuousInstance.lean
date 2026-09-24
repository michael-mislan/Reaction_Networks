import proofs.SerialTransferSelection.CountEnrichment
import proofs.SerialTransferSelection.CandidateErrors
import proofs.SerialTransferSelection.UniformClocks
import proofs.SerialTransferSelection.InitialPopulation
import proofs.SerialTransferSelection.ChemicalReadout

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem sourceCycleError_split (N M JB JR : ℕ) (qb qr t p ε : ℝ) :
    sourceCycleError N M JB JR qb qr t p ε =
      nonserviceCycleError N M t p ε+t*qb/JB+(M : ℝ)*(5376*qr/JR) := by
  unfold sourceCycleError nonserviceCycleError
  ring

theorem candidate_two_cycle_error (JB JR : ℕ) (qb qr : ℝ)
    (hb : candidateTime*qb/JB < 1/1000)
    (hr : (candidateM : ℝ)*(5376*qr/JR) < 1/1000) :
    sourceCycleError candidateN candidateM JB JR qb qr candidateTime (1/2) (1/50)+
      sourceCycleError candidateN candidateM JB JR qb qr candidateTime (1/100) (1/50) < 1/100 := by
  rw [sourceCycleError_split,sourceCycleError_split]
  have h0 := candidate_nonservice_error (1/2) (by norm_num)
  have h1 := candidate_nonservice_error (1/100) le_rfl
  linarith only [h0,h1,hb,hr]

def realizedCountGain (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (y : ReadyPopulation N M zL zH) : Prop :=
  retainedCountGain N M zL zH s y ∧ ∀ c ∈ y.val.live, chemicalReadout c=c.high

/-- A nonempty finite source instance, with all root, initial-state, clock and
quota assumptions discharged. Quotas are finite existence witnesses; the
maintained resident source is not replaced by depleting autonomous reservoirs. -/
theorem nonvacuous_serial_count_instance :
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
        (∀ b, ancestralCount b s.val.live=500000000000000) ∧
        (∀ c ∈ s.val.live, chemicalReadout c=c.high) ∧
        (99/100 : ℝ) ≤
          (sourceTwoCycleLaw candidateN candidateM JB JR (by norm_num [candidateN])
            (by norm_num [candidateM]) zL zH hzL hzH qr hqr hclockr candidateGamma
            (by norm_num [candidateGamma]) qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb s).expect
            (FiniteKernel.eventIndicator (successfulOutput (realizedCountGain candidateN candidateM zL zH s.val))) := by
  obtain ⟨zL,hzL,hsL⟩ := low_source_root
  obtain ⟨zH,hzH,hsH⟩ := high_source_root
  obtain ⟨qb,qr,hqb,hqr,hkb,hkr,hclockb,hclockr⟩ := exists_uniform_source_clocks candidateN candidateM
    zL zH candidateGamma (by norm_num [candidateGamma])
    ((9/40000)*(candidateN : ℝ)*candidateGamma) ((candidateN : ℝ)*localAlpha*innerEnergy/672)
  obtain ⟨JB,JR,hJB,hJR,hb,hr⟩ := exists_uniform_cycle_quotas candidateM (by norm_num [candidateM])
    qb qr candidateTime (1/1000) (by norm_num)
  obtain ⟨s,hcounts⟩ := balanced_initial_nonempty candidateN 500000000000000
    (by norm_num [candidateN]) zL zH hzL hzH
  have hfloor (b : Bool) : (1/2 : ℝ)*(candidateM : ℝ) ≤ ancestralCount b s.val.live := by
    rw [hcounts b]
    norm_num [candidateM]
  have hprob := sourceTwoCycle_count_probability candidateN candidateM JB JR (by norm_num [candidateN])
    (by norm_num [candidateM]) zL zH hzL hzH qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
    qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb hsL hsH (by norm_num [candidateN])
    (by norm_num [candidateN]) hJB hJR (by norm_num [candidateGamma]) (by norm_num [candidateGamma])
    hkr hkb (by change candidateTime=8/candidateGamma; norm_num [candidateTime,candidateGamma]) s hfloor
  have herr := candidate_two_cycle_error JB JR qb qr hb hr
  refine ⟨zL,zH,hzL,hzH,hsL,hsH,JB,JR,qb,qr,hqb,hqr,hclockr,hclockb,s,
    hJB,hJR,hb,hr,hcounts,?_,?_⟩
  · exact fun c hc => ready_population_readout candidateN candidateM zL zH hzL hzH s c hc
  · have hmono := finiteLaw_successful_mono
      (sourceTwoCycleLaw candidateN candidateM JB JR (by norm_num [candidateN])
        (by norm_num [candidateM]) zL zH hzL hzH qr hqr hclockr candidateGamma
        (by norm_num [candidateGamma]) qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb s)
      (retainedCountGain candidateN candidateM zL zH s.val)
      (realizedCountGain candidateN candidateM zL zH s.val) (fun y hy =>
        ⟨hy,fun c hc => ready_population_readout candidateN candidateM zL zH hzL hzH y c hc⟩)
    exact (by linarith only [herr] : (99/100 : ℝ) ≤
      1-(sourceCycleError candidateN candidateM JB JR qb qr candidateTime (1/2) (1/50)+
        sourceCycleError candidateN candidateM JB JR qb qr candidateTime (1/100) (1/50))).trans
      (hprob.trans hmono)

end SerialTransferSelection
