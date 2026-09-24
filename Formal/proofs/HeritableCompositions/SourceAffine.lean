import proofs.HeritableCompositions.GrowthWellBounds

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem low_growth_local_affine (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N) (c : Compartment) (hNm : N ≤ c.2)
    (he : lowEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator γ
      (fun d => lowExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*
        lowExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1)+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : pointOfState (lift sourceRates z) 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (lowroot_upper z hz) hsz
    lowEnergy lowEnergy_lower he
  have hlocal := low_growing_generator_bound z γ hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  have hupper : lowEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) ≤
      42*normSq (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) := by
    nlinarith only [lowEnergy_upper (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i),
      normSq_nonneg (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i)]
  rw [compartment_generator_binding γ c.2 (by omega) c.1]
  exact hlocal.trans (growing_affine_recovery N γ _ _ hlarge hγ hγmax (normSq_nonneg _) hupper)

theorem high_growth_local_affine (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N) (c : Compartment) (hNm : N ≤ c.2)
    (he : highEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator γ
      (fun d => highExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*
        highExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1)+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : pointOfState (lift sourceRates z) 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (highroot_upper z hz) hsz
    highEnergy highEnergy_lower he
  have hlocal := high_growing_generator_bound z γ hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  have hupper := highEnergy_upper (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i)
  simp only [div_one] at hupper
  rw [compartment_generator_binding γ c.2 (by omega) c.1]
  exact hlocal.trans (growing_affine_recovery N γ _ _ hlarge hγ hγmax (normSq_nonneg _) hupper)

end HeritableCompositions
