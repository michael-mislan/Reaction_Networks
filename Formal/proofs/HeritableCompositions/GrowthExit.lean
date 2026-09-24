import proofs.HeritableCompositions.GrowthWellBounds

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem growth_energy_exit_bound (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (s : Point) (hs : ∀ i, s i ≤ 34) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y) (b B : ℝ)
    (hb : b ≤ 1/32000000) (hB : 0 ≤ B)
    (hgen : ∀ c ∈ growthDomain N s E b, c.2 < 2*N →
      compartmentGenerator γ (fun d => Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration d.2 d.1 i-s i))) c ≤ B)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N (growthDomain N s E b)).total c ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N s E b}) :
    Real.exp ((N : ℝ)*localAlpha*b)*
      ((stoppedGrowthModel γ hγ N (growthDomain N s E b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some c) ≤
      Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration c.val.2 c.val.1 i-s i))+(t : ℝ)*B := by
  apply stopped_growth_event_bound γ hγ N (growthDomain N s E b)
    (fun d => Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration d.2 d.1 i-s i)))
    (Real.exp ((N : ℝ)*localAlpha*b)) B (Real.exp_pos _).le hB
  · intro d _
    exact (Real.exp_pos _).le
  · intro d hd hm r hout
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (growth_domain_departure_energy N hN s hs E hE b hb d hd hm r hout)
      (by unfold localAlpha; positivity)
  · exact hgen

theorem low_growth_exit_bound (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : b ≤ 1/32000000)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N
      (growthDomain N (pointOfState (lift sourceRates z)) lowEnergy b)).total c ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N (pointOfState (lift sourceRates z)) lowEnergy b}) :
    Real.exp ((N : ℝ)*localAlpha*b)*
      ((stoppedGrowthModel γ hγ N (growthDomain N (pointOfState (lift sourceRates z)) lowEnergy b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some c) ≤
      lowExponential N (pointOfState (lift sourceRates z)) (concentration c.val.2 c.val.1)+(t : ℝ)*growingCeiling N γ := by
  apply growth_energy_exit_bound γ hγ N hN _ (lowroot_upper z hz) lowEnergy lowEnergy_lower b
    (growingCeiling N γ) hb (growingCeiling_nonneg N γ (Nat.cast_nonneg N))
  intro d hd _
  have hm := (mem_growthDomain N hN d _ (lowroot_upper z hz) lowEnergy lowEnergy_lower b hb).mp hd
  exact low_growth_local_ceiling z γ hz hstationary hγ hγmax N hN d hm.1 (hm.2.2.trans_le hb)

theorem high_growth_exit_bound (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : b ≤ 1/32000000)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N
      (growthDomain N (pointOfState (lift sourceRates z)) highEnergy b)).total c ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N (pointOfState (lift sourceRates z)) highEnergy b}) :
    Real.exp ((N : ℝ)*localAlpha*b)*
      ((stoppedGrowthModel γ hγ N (growthDomain N (pointOfState (lift sourceRates z)) highEnergy b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some c) ≤
      highExponential N (pointOfState (lift sourceRates z)) (concentration c.val.2 c.val.1)+(t : ℝ)*growingCeiling N γ := by
  apply growth_energy_exit_bound γ hγ N hN _ (highroot_upper z hz) highEnergy highEnergy_lower b
    (growingCeiling N γ) hb (growingCeiling_nonneg N γ (Nat.cast_nonneg N))
  intro d hd _
  have hm := (mem_growthDomain N hN d _ (highroot_upper z hz) highEnergy highEnergy_lower b hb).mp hd
  exact high_growth_local_ceiling z γ hz hstationary hγ hγmax N hN d hm.1 (hm.2.2.trans_le hb)

end HeritableCompositions
