import proofs.ProductiveMemory.ExtractionCompartment
import proofs.ProductiveMemory.ExtractionGrowthEnvelope
import proofs.ProductiveMemory.ExtractionWell
import proofs.HeritableCompositions.GrowthWellBounds

namespace ProductiveMemory
open FiniteCopy HeritableCompositions Set
noncomputable section
set_option Elab.async false

theorem low_extraction_growth_ceiling (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hstationary : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N)
    (c : Compartment) (hNm : N ≤ c.2)
    (he : lowExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    growingCompartmentGenerator rho γ
      (fun d => energyExponential lowExtractionEnergy N (lift rho z) (concentration d.2 d.1)) c ≤
      extractionGrowingCeiling N γ := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : lift rho z 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (low_extraction_root_upper rho z hr hz) hsz
    lowExtractionEnergy lowExtractionEnergy_lower he
  have hlocal := low_extraction_growing_bound rho z γ hr hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (low_extraction_root_upper rho z hr hz)
  rw [growing_compartment_binding rho γ c.2 (by omega) c.1]
  exact hlocal.trans (extraction_growing_envelope N γ _ _ (Nat.cast_nonneg N) (normSq_nonneg _) (lowExtractionEnergy_upper _))

theorem low_extraction_growth_affine (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hstationary : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2)
    (he : lowExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    growingCompartmentGenerator rho γ
      (fun d => energyExponential lowExtractionEnergy N (lift rho z) (concentration d.2 d.1)) c ≤
      -((N:ℝ)*localAlpha*innerEnergy/960)*
        energyExponential lowExtractionEnergy N (lift rho z) (concentration c.2 c.1)+
      ((N:ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N:ℝ)*localAlpha*innerEnergy/2)) := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : lift rho z 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (low_extraction_root_upper rho z hr hz) hsz
    lowExtractionEnergy lowExtractionEnergy_lower he
  have hlocal := low_extraction_growing_bound rho z γ hr hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (low_extraction_root_upper rho z hr hz)
  rw [growing_compartment_binding rho γ c.2 (by omega) c.1]
  exact hlocal.trans (extraction_growing_affine N γ _ _ hlarge hγ hγmax (normSq_nonneg _) (lowExtractionEnergy_upper _))

theorem high_extraction_growth_ceiling (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hstationary : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N)
    (c : Compartment) (hNm : N ≤ c.2)
    (he : highExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    growingCompartmentGenerator rho γ
      (fun d => energyExponential highExtractionEnergy N (lift rho z) (concentration d.2 d.1)) c ≤
      extractionGrowingCeiling N γ := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : lift rho z 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (high_extraction_root_upper rho z hr hz) hsz
    highExtractionEnergy highExtractionEnergy_lower he
  have hlocal := high_extraction_growing_bound rho z γ hr hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (high_extraction_root_upper rho z hr hz)
  rw [growing_compartment_binding rho γ c.2 (by omega) c.1]
  exact hlocal.trans (extraction_growing_envelope N γ _ _ (Nat.cast_nonneg N) (normSq_nonneg _) (highExtractionEnergy_upper _))

theorem high_extraction_growth_affine (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hstationary : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (N : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2)
    (he : highExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    growingCompartmentGenerator rho γ
      (fun d => energyExponential highExtractionEnergy N (lift rho z) (concentration d.2 d.1)) c ≤
      -((N:ℝ)*localAlpha*innerEnergy/960)*
        energyExponential highExtractionEnergy N (lift rho z) (concentration c.2 c.1)+
      ((N:ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N:ℝ)*localAlpha*innerEnergy/2)) := by
  have hm : 1 ≤ c.2 := hN.trans hNm
  have hsz : lift rho z 2 ≤ 3 := by
    change z ≤ 3
    linarith only [hz.2]
  have hg := small_growth_energy_geometry c.2 c.1 _ (high_extraction_root_upper rho z hr hz) hsz
    highExtractionEnergy highExtractionEnergy_lower he
  have hlocal := high_extraction_growing_bound rho z γ hr hz hstationary hγ hγmax N c.2 hm hNm c.1
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (high_extraction_root_upper rho z hr hz)
  rw [growing_compartment_binding rho γ c.2 (by omega) c.1]
  exact hlocal.trans (extraction_growing_affine N γ _ _ hlarge hγ hγmax (normSq_nonneg _) (highExtractionEnergy_upper _))

end
end ProductiveMemory
