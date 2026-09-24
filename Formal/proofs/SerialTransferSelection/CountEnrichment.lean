import proofs.SerialTransferSelection.TwoCycle
import proofs.SerialTransferSelection.PopulationPhase
import proofs.SerialTransferSelection.ParameterMargins

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def retainedCountGain (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (y : ReadyPopulation N M zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.val.live) ∧
    519/12250 < countLogOdds y.val-countLogOdds s

theorem sourceTwoCycle_count_probability (N M JB JR : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (qr : NNReal) (hqr : 0 < (qr : ℝ))
    (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)
    (γ : ℝ) (hγ : 0 ≤ γ) (qb t : NNReal) (hqb : 0 < (qb : ℝ))
    (hclockb : ∀ (s : ReadyPopulation N M zL zH) x, (cycleBatchModel N M zL zH γ hγ s).total x ≤ qb)
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (h1000 : 1000 ≤ N)
    (hJB : 0 < JB) (hJR : 0 < JR) (hγpos : 0 < γ) (hγmax : γ ≤ 1/100000000000)
    (hkr : (N : ℝ)*localAlpha*innerEnergy/672 ≤ qr)
    (hkb : (9/40000)*(N : ℝ)*γ ≤ qb) (htime : (t : ℝ)=8/γ)
    (s : ReadyPopulation N M zL zH)
    (hfloor : ∀ b, (1/2 : ℝ)*(M : ℝ) ≤ ancestralCount b s.val.live) :
    1-(sourceCycleError N M JB JR qb qr t (1/2) (1/50)+sourceCycleError N M JB JR qb qr t (1/100) (1/50)) ≤
      (sourceTwoCycleLaw N M JB JR hN hM zL zH hzL hzH qr hqr hclockr γ hγ qb t hqb hclockb s).expect
        (FiniteKernel.eventIndicator (successfulOutput (retainedCountGain N M zL zH s.val))) := by
  have h := sourceTwoCycleLaw_probability N M JB JR hN hM zL zH hzL hzH qr hqr hclockr
    γ hγ qb t hqb hclockb hsL hsH hlarge h1000 hJB hJR hγpos hγmax hkr hkb htime
    (1/2) (1/100) (1/50) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) s hfloor
  apply h.trans
  apply finiteLaw_successful_mono
  intro y hy
  have hcs (b : Bool) : 0 < ancestralCount b s.val.live := by
    have hp : (0 : ℝ) < (1/2 : ℝ)*M := by positivity
    exact_mod_cast hp.trans_le (hfloor b)
  have hc := endpoint_count_gain N (by omega) s.val y.val
    (readyPopulation_ready N M zL zH s).2.2.2.1
    (readyPopulation_ready N M zL zH y).2.2.2.1 hcs hy.1 _ hy.2
  have hm : (519/12250 : ℝ) ≤ 2*cycleSizeGain (1/50)-2*Real.log 2 := by
    exact two_cycle_count_gain_lower
  exact ⟨hy.1,hm.trans_lt hc⟩

end SerialTransferSelection
