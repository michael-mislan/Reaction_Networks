import proofs.ProductiveMemory.ExtractionSpatial
import proofs.ProductiveMemory.ExtractionCellGeometry
import proofs.ResourceLimitedCompetition.SpatialReset

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
noncomputable section
set_option Elab.async false

theorem low_extraction_growth_ratio (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2) (hn : 1 ≤ c.1 2)
    (he : lowExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    energyExponential lowExtractionEnergy N (lift rho z) (concentration (nextCompartment c (.inr ())).2 (nextCompartment c (.inr ())).1) ≤
      2*energyExponential lowExtractionEnergy N (lift rho z) (concentration c.2 c.1) := by
  apply extraction_source_growth_ratio lowExtractionEnergy lowExtractionPair low_extraction_energy_sub lowExtractionEnergy_lower
    low_extraction_membrane_energy low_extraction_pair_box _
    (low_extraction_root_upper rho z hr hz) _ N hN c hNm hn he
  change z ≤ 3
  linarith only [hz.2]

theorem low_extraction_resource_spatial (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hs : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (200000000000000000000:ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2) (hmmax : c.2 ≤ 2*N)
    (he : lowExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    growingCompartmentGenerator rho (resourceCoefficient γ Q Ω)
      (fun d => spatialWeight (1/1000000000000000) N d.2*
        energyExponential lowExtractionEnergy N (lift rho z) (concentration d.2 d.1)) c ≤
      -(((N:ℝ)*localAlpha*innerEnergy/960)/2)*
        (spatialWeight (1/1000000000000000) N c.2*energyExponential lowExtractionEnergy N (lift rho z) (concentration c.2 c.1))+
      ((N:ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N:ℝ)*localAlpha*innerEnergy/2)) := by
  have hzbound := low_outer_readout rho z hz (concentration c.2 c.1) he.le
  have hn : 1 ≤ c.1 2 := by
    by_contra h
    have hzero : c.1 2=0 := by omega
    have hlo := hzbound.1
    norm_num [concentration,hzero] at hlo
  obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ Q Ω hγ hQ
  apply extraction_compartment_spatial_bound rho _ hb (hbmax.trans hγmax) N c (by omega) hmmax
    (hzbound.2.trans (by norm_num))
    (fun d => energyExponential lowExtractionEnergy N (lift rho z) (concentration d.2 d.1))
    (fun d => (Real.exp_pos _).le)
    (low_extraction_growth_ratio rho z hr hz N hN c hNm hn he)
  exact low_extraction_growth_affine rho z _ hr hz hs hb (hbmax.trans hγmax) N hN hlarge c hNm he

theorem high_extraction_growth_ratio (rho z : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (N : ℕ) (hN : 1 ≤ N) (c : Compartment) (hNm : N ≤ c.2) (hn : 1 ≤ c.1 2)
    (he : highExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    energyExponential highExtractionEnergy N (lift rho z) (concentration (nextCompartment c (.inr ())).2 (nextCompartment c (.inr ())).1) ≤
      2*energyExponential highExtractionEnergy N (lift rho z) (concentration c.2 c.1) := by
  apply extraction_source_growth_ratio highExtractionEnergy highExtractionPair high_extraction_energy_sub highExtractionEnergy_lower
    high_extraction_membrane_energy high_extraction_pair_box _
    (high_extraction_root_upper rho z hr hz) _ N hN c hNm hn he
  change z ≤ 3
  linarith only [hz.2]

theorem high_extraction_resource_spatial (rho z γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hz : z ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hs : extractDrift rho 0 (lift rho z) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (200000000000000000000:ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2) (hmmax : c.2 ≤ 2*N)
    (he : highExtractionEnergy (fun i => concentration c.2 c.1 i-lift rho z i) < outerLevel) :
    growingCompartmentGenerator rho (resourceCoefficient γ Q Ω)
      (fun d => spatialWeight (1/1000000000000000) N d.2*
        energyExponential highExtractionEnergy N (lift rho z) (concentration d.2 d.1)) c ≤
      -(((N:ℝ)*localAlpha*innerEnergy/960)/2)*
        (spatialWeight (1/1000000000000000) N c.2*energyExponential highExtractionEnergy N (lift rho z) (concentration c.2 c.1))+
      ((N:ℝ)*localAlpha*innerEnergy/960)*(2*Real.exp ((N:ℝ)*localAlpha*innerEnergy/2)) := by
  have hzbound := high_outer_readout rho z hz (concentration c.2 c.1) he.le
  have hn : 1 ≤ c.1 2 := by
    by_contra h
    have hzero : c.1 2=0 := by omega
    have hlo := hzbound.1
    norm_num [concentration,hzero] at hlo
  obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ Q Ω hγ hQ
  apply extraction_compartment_spatial_bound rho _ hb (hbmax.trans hγmax) N c (by omega) hmmax
    (hzbound.2.trans (by norm_num))
    (fun d => energyExponential highExtractionEnergy N (lift rho z) (concentration d.2 d.1))
    (fun d => (Real.exp_pos _).le)
    (high_extraction_growth_ratio rho z hr hz N hN c hNm hn he)
  exact high_extraction_growth_affine rho z _ hr hz hs hb (hbmax.trans hγmax) N hN hlarge c hNm he

def extractionCellSpatial (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell) : ℝ :=
  spatialWeight (1/1000000000000000) N c.compartment.2*
    Real.exp ((N:ℝ)*localAlpha*extractionCellEnergy rho zL zH c)

theorem extraction_spatial_nonneg (N : ℕ) (rho zL zH : ℝ) (c : TaggedCell) :
    0 ≤ extractionCellSpatial N rho zL zH c := by
  unfold extractionCellSpatial spatialWeight; positivity

end
end ProductiveMemory
