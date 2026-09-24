import proofs.SerialTransferSelection.NewbornProbability
import proofs.SerialTransferSelection.PostproofParameters
import proofs.SerialTransferSelection.MeasuredCounts

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def newbornMeasuredGain (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (y : ReadyPopulation N M zL zH) : Prop :=
  (∀ b, 0 < chemicalCount b y.val.live) ∧
    2*cycleSizeGain (1/50)-Real.log 2 < chemicalCountLogOdds y.val-chemicalCountLogOdds s

theorem newborn_gain_measured (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (hs : ∀ c ∈ s.live, chemicalReadout c=c.high) (y : ReadyPopulation N M zL zH)
    (hy : ∀ c ∈ y.val.live, chemicalReadout c=c.high)
    (hg : newbornCountGain N M zL zH s y) : newbornMeasuredGain N M zL zH s y := by
  constructor
  · intro b
    rw [chemicalCount_eq_ancestralCount b y.val.live hy]
    exact hg.1 b
  · rw [chemicalCountLogOdds_eq y.val hy,chemicalCountLogOdds_eq s hs]
    exact hg.2

theorem improved_serial_instance (N K : ℕ)
    (hN : 140000000000000000000 ≤ N) (hK : 0 < K) (confidence : ℝ)
    (herror : ∀ (JB JR : ℕ) (qb qr : ℝ),
      candidateTime*qb/JB < 1/1000 → (2*K : ℕ)*(5376*qr/JR) < 1/1000 →
      sourceCycleError N (2*K) JB JR qb qr candidateTime (1/2) (1/50)+
      sourceCycleError N (2*K) JB JR qb qr candidateTime (1/100) (1/50) < 1-confidence) :
    ∃ (zL zH : ℝ)
      (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
      (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)),
      Stationary sourceRates (lift sourceRates zL) ∧ Stationary sourceRates (lift sourceRates zH) ∧
      ∃ (JB JR : ℕ) (qb qr : NNReal) (hqb : 0 < (qb : ℝ)) (hqr : 0 < (qr : ℝ))
        (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
        (hclockb : ∀ (s : ReadyPopulation N (2*K) zL zH) x,
          (cycleBatchModel N (2*K) zL zH candidateGamma (by norm_num [candidateGamma]) s).total x ≤ qb)
        (s : ReadyPopulation N (2*K) zL zH),
        0 < JB ∧ 0 < JR ∧ candidateTime*(qb : ℝ)/JB < 1/1000 ∧
        ((2*K : ℕ) : ℝ)*(5376*(qr : ℝ)/JR) < 1/1000 ∧
        (∀ b, chemicalCount b s.val.live=K) ∧
        (∀ c ∈ s.val.live, c.compartment.2=N) ∧
        (∀ c ∈ s.val.live, chemicalReadout c=c.high) ∧
        confidence ≤
          (sourceTwoCycleLaw N (2*K) JB JR (by omega)
            (by omega) zL zH hzL hzH qr hqr hclockr candidateGamma
            (by norm_num [candidateGamma]) qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb s).expect
            (FiniteKernel.eventIndicator (successfulOutput (newbornMeasuredGain N (2*K) zL zH s.val))) := by
  obtain ⟨zL,hzL,hsL⟩ := low_source_root
  obtain ⟨zH,hzH,hsH⟩ := high_source_root
  obtain ⟨qb,qr,hqb,hqr,hkb,hkr,hclockb,hclockr⟩ := exists_uniform_source_clocks N (2*K)
    zL zH candidateGamma (by norm_num [candidateGamma])
    ((9/40000)*(N : ℝ)*candidateGamma) ((N : ℝ)*localAlpha*innerEnergy/672)
  obtain ⟨JB,JR,hJB,hJR,hb,hr⟩ := exists_uniform_cycle_quotas (2*K) (by omega)
    qb qr candidateTime (1/1000) (by norm_num)
  obtain ⟨s,hcounts,hnew⟩ := balanced_initial_newborn N K
    (by omega) zL zH hzL hzH
  have hfloor (b : Bool) : (1/2 : ℝ)*((2*K : ℕ) : ℝ) ≤ ancestralCount b s.val.live := by
    rw [hcounts b]
    push_cast
    linarith
  have hprob := sourceTwoCycle_newborn_probability N (2*K) JB JR (by omega)
    (by omega) zL zH hzL hzH qr hqr hclockr candidateGamma (by norm_num [candidateGamma])
    qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb hsL hsH (by exact_mod_cast hN)
    (by omega) hJB hJR (by norm_num [candidateGamma]) (by norm_num [candidateGamma])
    hkr hkb (by change candidateTime=8/candidateGamma; norm_num [candidateTime,candidateGamma]) s hfloor hnew
  have herr := herror JB JR qb qr hb hr
  refine ⟨zL,zH,hzL,hzH,hsL,hsH,JB,JR,qb,qr,hqb,hqr,hclockr,hclockb,s,
    hJB,hJR,hb,hr,?_,hnew,?_,?_⟩
  · intro b
    rw [chemicalCount_eq_ancestralCount b s.val.live (fun c hc => ready_population_readout N (2*K) zL zH hzL hzH s c hc)]
    exact hcounts b
  · exact fun c hc => ready_population_readout N (2*K) zL zH hzL hzH s c hc
  · have hmono := finiteLaw_successful_mono
      (sourceTwoCycleLaw N (2*K) JB JR (by omega)
        (by omega) zL zH hzL hzH qr hqr hclockr candidateGamma
        (by norm_num [candidateGamma]) qb ⟨candidateTime,by norm_num [candidateTime]⟩ hqb hclockb s)
      (newbornCountGain N (2*K) zL zH s.val)
      (newbornMeasuredGain N (2*K) zL zH s.val) (fun y hy =>
        newborn_gain_measured N (2*K) zL zH s.val
          (fun c hc => ready_population_readout N (2*K) zL zH hzL hzH s c hc) y
          (fun c hc => ready_population_readout N (2*K) zL zH hzL hzH y c hc) hy)
    exact (by linarith only [herr] : confidence ≤
      1-(sourceCycleError N (2*K) JB JR qb qr candidateTime (1/2) (1/50)+
        sourceCycleError N (2*K) JB JR qb qr candidateTime (1/100) (1/50))).trans
      (hprob.trans hmono)

end SerialTransferSelection
