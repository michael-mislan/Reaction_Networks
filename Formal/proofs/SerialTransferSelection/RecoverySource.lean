import proofs.SerialTransferSelection.RecoveryReturn

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem low_endpoint_recovery (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N
      (growthDomain N (pointOfState (lift sourceRates z)) lowEnergy outerEnergy)).total c ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N (pointOfState (lift sourceRates z)) lowEnergy outerEnergy})
    (hc : c.val.2 < 2*N)
    (hbirth : lowEnergy (fun i => concentration c.val.2 c.val.1 i-pointOfState (lift sourceRates z) i) ≤ 8*innerEnergy) :
    ((stoppedGrowthModel γ hγ N (growthDomain N (pointOfState (lift sourceRates z)) lowEnergy outerEnergy)).uniformize q hq hclock).poissonized
      (q*5376) (FiniteKernel.eventIndicator (retainedUnrecovered N (pointOfState (lift sourceRates z)) lowEnergy)) (some c) ≤
      Real.exp (-((N : ℝ)*localAlpha*innerEnergy))+2*Real.exp (-((N : ℝ)*localAlpha*innerEnergy)/2) := by
  apply endpoint_terminal_recovery γ hγ N _ lowEnergy _ q hq hclock hk c hc hbirth
  intro d hd _
  have hmem : d ∈ growthDomain N (pointOfState (lift sourceRates z)) lowEnergy outerEnergy :=
    hd
  have hm := (mem_growthDomain N hN d _ (lowroot_upper z hz) lowEnergy lowEnergy_lower
    outerEnergy (by norm_num [outerEnergy])).mp hmem
  exact low_growth_local_affine z γ hz hstationary hγ hγmax N hN hlarge d hm.1 hm.2.2

theorem high_endpoint_recovery (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N
      (growthDomain N (pointOfState (lift sourceRates z)) highEnergy outerEnergy)).total c ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N (pointOfState (lift sourceRates z)) highEnergy outerEnergy})
    (hc : c.val.2 < 2*N)
    (hbirth : highEnergy (fun i => concentration c.val.2 c.val.1 i-pointOfState (lift sourceRates z) i) ≤ 8*innerEnergy) :
    ((stoppedGrowthModel γ hγ N (growthDomain N (pointOfState (lift sourceRates z)) highEnergy outerEnergy)).uniformize q hq hclock).poissonized
      (q*5376) (FiniteKernel.eventIndicator (retainedUnrecovered N (pointOfState (lift sourceRates z)) highEnergy)) (some c) ≤
      Real.exp (-((N : ℝ)*localAlpha*innerEnergy))+2*Real.exp (-((N : ℝ)*localAlpha*innerEnergy)/2) := by
  apply endpoint_terminal_recovery γ hγ N _ highEnergy _ q hq hclock hk c hc hbirth
  intro d hd _
  have hmem : d ∈ growthDomain N (pointOfState (lift sourceRates z)) highEnergy outerEnergy :=
    hd
  have hm := (mem_growthDomain N hN d _ (highroot_upper z hz) highEnergy highEnergy_lower
    outerEnergy (by norm_num [outerEnergy])).mp hmem
  exact high_growth_local_affine z γ hz hstationary hγ hγmax N hN hlarge d hm.1 hm.2.2

end SerialTransferSelection



