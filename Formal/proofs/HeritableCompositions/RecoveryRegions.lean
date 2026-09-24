import proofs.HeritableCompositions.SourceRecovery

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

theorem coordinate_le_radius (y : Point) (i : Fin 4) :
    |y i| ≤ Real.sqrt (normSq y) := by
  have hs := Real.sq_sqrt (normSq_nonneg y)
  have hr := Real.sqrt_nonneg (normSq y)
  have hc := coordinate_sq_le_normSq y i
  nlinarith only [hs, hr, hc, sq_abs (y i), abs_nonneg (y i)]

theorem low_annular_source_decay (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (y : Point)
    (hy : ∀ i, |y i| ≤ 1/400) (ha : innerEnergy ≤ lowEnergy y)
    (hxz : 0 ≤ pointOfState (lift sourceRates z) 2+y 2 ∧
      pointOfState (lift sourceRates z) 2+y 2 ≤ 4)
    (hx : ∀ i, |pointOfState (lift sourceRates z) i+y i+membraneDirection i| ≤ 36) :
    2*lowPair y (growthField γ (fun i => pointOfState (lift sourceRates z) i+y i)) ≤
      -(59/8400)*lowEnergy y := by
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hu : lowEnergy y ≤ 42*r^2 := by
    rw [hsq]
    linarith only [lowEnergy_upper y, normSq_nonneg y]
  have hd := low_source_dissipation z hz hs y hy
  have hg := low_growth_perturbation γ r y
    (fun i => pointOfState (lift sourceRates z) i+y i) hγ hr hxz
    (coordinate_le_radius y) hx
  have hb := growth_absorption_budget γ r (lowEnergy y) hγ hγmax hr ha hu
  rw [hsq] at hu hb
  linarith only [hd, hg, hb, hu]

theorem high_annular_source_decay (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) (y : Point)
    (hy : ∀ i, |y i| ≤ 1/400) (ha : innerEnergy ≤ highEnergy y)
    (hxz : 0 ≤ pointOfState (lift sourceRates z) 2+y 2 ∧
      pointOfState (lift sourceRates z) 2+y 2 ≤ 4)
    (hx : ∀ i, |pointOfState (lift sourceRates z) i+y i+membraneDirection i| ≤ 36) :
    2*highPair y (growthField γ (fun i => pointOfState (lift sourceRates z) i+y i)) ≤
      -(59/8400)*highEnergy y := by
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hu : highEnergy y ≤ 42*r^2 := by rw [hsq]; simpa using highEnergy_upper y
  have hd := high_source_dissipation z hz hs y hy
  have hg := high_growth_perturbation γ r y
    (fun i => pointOfState (lift sourceRates z) i+y i) hγ hr hxz
    (coordinate_le_radius y) hx
  have hb := growth_absorption_budget γ r (highEnergy y) hγ hγmax hr ha hu
  rw [hsq] at hu hb
  linarith only [hd, hg, hb, hu]

end HeritableCompositions
