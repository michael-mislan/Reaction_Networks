import proofs.CompositionalMemory.ScalingLocalGenerator

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

theorem low_coupled_generator_bound {k : ℕ} (hk : 1 ≤ k)
    (zc γ κ m N : ℝ) (w : Fin k → ℝ) (i : Fin k) (n : Fin k → Counts)
    (hzc : zc ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates zc))
    (hN : 1 ≤ N) (hm : (k : ℝ)*N ≤ m)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hz : ∀ j, 0 ≤ effectiveConcentration (m/k) (n j) 2 ∧
      effectiveConcentration (m/k) (n j) 2 ≤ 4)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j ≤ κ)
    (hy : ∀ a, |effectiveConcentration (m/k) (n i) a-pointOfState (lift sourceRates zc) a| ≤ 1/400)
    (hnorm : normSq (fun a => effectiveConcentration (m/k) (n i) a-
      pointOfState (lift sourceRates zc) a) ≤ 1/160000)
    (hx : ∀ a, |effectiveConcentration (m/k) (n i) a| ≤ 35) :
    coupledLocalGenerator γ m w i n
      (fun x => Real.exp ((1/1000000000000 : ℝ)*N*
        lowEnergy (fun a => x a-pointOfState (lift sourceRates zc) a))) ≤
      (1/1000000000000 : ℝ)*Real.exp ((1/1000000000000 : ℝ)*N*
        lowEnergy (fun a => effectiveConcentration (m/k) (n i) a-pointOfState (lift sourceRates zc) a))*
        (-N*normSq (fun a => effectiveConcentration (m/k) (n i) a-
          pointOfState (lift sourceRates zc) a)/4+200000000+1200000000*N*(γ+κ)^2) := by
  let s := pointOfState (lift sourceRates zc)
  let x := effectiveConcentration (m/k) (n i)
  let y : Point := fun a => x a-s a
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hrmax : r ≤ 1/400 := by nlinarith only [hr,hrsq,hnorm]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hvN : N ≤ m/k := (le_div_iff₀ hkpos).mpr (by nlinarith only [hm])
  have hv : 1 ≤ m/k := hN.trans hvN
  have hres := low_effective_birth_bound zc N (m/k) hzc hstationary
    (by linarith only [hN]) hv hvN (n i) hy
  have heq : lowVolumeExponential N s =
      (fun v => Real.exp ((1/1000000000000 : ℝ)*N*lowEnergy (fun a => v a-s a))) := by
    funext v
    unfold lowVolumeExponential localAlpha
    congr 1
    ring
  change effectiveGenerator (1/100000) (m/k) (lowVolumeExponential N s) x ≤
    localAlpha*lowVolumeExponential N s x*(-N/2*normSq y+100000000) at hres
  rw [heq] at hres
  have h := coupled_bound_from_resident hk lowEnergyData γ κ m N r w i n s
    hN hm hγ hγmax hκ hκmax hz hw hs hr hrmax hrsq.symm (coordinate_box_norm x hx)
    (by
      dsimp only [lowEnergyData]
      rw [hrsq]
      unfold localAlpha at hres
      nlinarith only [hres])
  simpa only [lowEnergyData,hrsq,x,y,s] using h

theorem high_coupled_generator_bound {k : ℕ} (hk : 1 ≤ k)
    (zc γ κ m N : ℝ) (w : Fin k → ℝ) (i : Fin k) (n : Fin k → Counts)
    (hzc : zc ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates zc))
    (hN : 1 ≤ N) (hm : (k : ℝ)*N ≤ m)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hz : ∀ j, 0 ≤ effectiveConcentration (m/k) (n j) 2 ∧
      effectiveConcentration (m/k) (n j) 2 ≤ 4)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j ≤ κ)
    (hy : ∀ a, |effectiveConcentration (m/k) (n i) a-pointOfState (lift sourceRates zc) a| ≤ 1/400)
    (hnorm : normSq (fun a => effectiveConcentration (m/k) (n i) a-
      pointOfState (lift sourceRates zc) a) ≤ 1/160000)
    (hx : ∀ a, |effectiveConcentration (m/k) (n i) a| ≤ 35) :
    coupledLocalGenerator γ m w i n
      (fun x => Real.exp ((1/1000000000000 : ℝ)*N*
        highEnergy (fun a => x a-pointOfState (lift sourceRates zc) a))) ≤
      (1/1000000000000 : ℝ)*Real.exp ((1/1000000000000 : ℝ)*N*
        highEnergy (fun a => effectiveConcentration (m/k) (n i) a-pointOfState (lift sourceRates zc) a))*
        (-N*normSq (fun a => effectiveConcentration (m/k) (n i) a-
          pointOfState (lift sourceRates zc) a)/4+200000000+1200000000*N*(γ+κ)^2) := by
  let s := pointOfState (lift sourceRates zc)
  let x := effectiveConcentration (m/k) (n i)
  let y : Point := fun a => x a-s a
  let r := Real.sqrt (normSq y)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2=normSq y := Real.sq_sqrt (normSq_nonneg y)
  have hrmax : r ≤ 1/400 := by nlinarith only [hr,hrsq,hnorm]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hvN : N ≤ m/k := (le_div_iff₀ hkpos).mpr (by nlinarith only [hm])
  have hv : 1 ≤ m/k := hN.trans hvN
  have hres := high_effective_birth_bound zc N (m/k) hzc hstationary
    (by linarith only [hN]) hv hvN (n i) hy
  have heq : highVolumeExponential N s =
      (fun v => Real.exp ((1/1000000000000 : ℝ)*N*highEnergy (fun a => v a-s a))) := by
    funext v
    unfold highVolumeExponential localAlpha
    congr 1
    ring
  change effectiveGenerator (1/100000) (m/k) (highVolumeExponential N s) x ≤
    localAlpha*highVolumeExponential N s x*(-N/2*normSq y+100000000) at hres
  rw [heq] at hres
  have h := coupled_bound_from_resident hk highEnergyData γ κ m N r w i n s
    hN hm hγ hγmax hκ hκmax hz hw hs hr hrmax hrsq.symm (coordinate_box_norm x hx)
    (by
      dsimp only [highEnergyData]
      rw [hrsq]
      unfold localAlpha at hres
      nlinarith only [hres])
  simpa only [highEnergyData,hrsq,x,y,s] using h

end CompositionalMemory
