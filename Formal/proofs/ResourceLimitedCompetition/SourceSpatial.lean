import proofs.ResourceLimitedCompetition.SourceDivisionBarrier
import proofs.ResourceLimitedCompetition.SafeGeometry

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem low_resource_spatial_bound (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2) (hmmax : c.2 ≤ 2*N)
    (he : lowEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator (resourceCoefficient γ Q Ω)
      (fun d => spatialWeight (1/1000000000000000) N d.2*
        lowExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      -(((N : ℝ)*localAlpha*innerEnergy/672)/2)*
        (spatialWeight (1/1000000000000000) N c.2*
          lowExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  have hg := low_safe_geometry z hz (concentration c.2 c.1) he.le
  have hn : 1 ≤ c.1 2 := by
    by_contra h
    have hzero : c.1 2=0 := by omega
    have hlow := hg.1.1
    norm_num [concentration,hzero] at hlow
  obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ Q Ω hγ hQ
  apply compartment_spatial_bound _ hb (hbmax.trans hγmax) N c (by omega) hmmax
    (hg.1.2.trans (by norm_num))
    (fun d => lowExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1))
    (fun d => (Real.exp_pos _).le)
    (low_source_growth_ratio z hz N hN c hNm hn he)
  exact low_resource_local_affine z γ hz hs hγ hγmax Q Ω hQ N hN hlarge c hNm he

theorem high_resource_spatial_bound (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (Q Ω : ℕ) (hQ : Q ≤ Ω)
    (N : ℕ) (hN : 1 ≤ N) (hlarge : (140000000000000000000 : ℝ) ≤ N)
    (c : Compartment) (hNm : N ≤ c.2) (hmmax : c.2 ≤ 2*N)
    (he : highEnergy (fun i => concentration c.2 c.1 i-pointOfState (lift sourceRates z) i) < 1/32000000) :
    compartmentGenerator (resourceCoefficient γ Q Ω)
      (fun d => spatialWeight (1/1000000000000000) N d.2*
        highExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1)) c ≤
      -(((N : ℝ)*localAlpha*innerEnergy/672)/2)*
        (spatialWeight (1/1000000000000000) N c.2*
          highExponential N (pointOfState (lift sourceRates z)) (concentration c.2 c.1))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)) := by
  have hg := high_safe_geometry z hz (concentration c.2 c.1) he.le
  have hn : 1 ≤ c.1 2 := by
    by_contra h
    have hzero : c.1 2=0 := by omega
    have hlow := hg.1.1
    norm_num [concentration,hzero] at hlow
  obtain ⟨hb,hbmax⟩ := resource_coefficient_bounds γ Q Ω hγ hQ
  apply compartment_spatial_bound _ hb (hbmax.trans hγmax) N c (by omega) hmmax
    (hg.1.2.trans (by norm_num))
    (fun d => highExponential N (pointOfState (lift sourceRates z)) (concentration d.2 d.1))
    (fun d => (Real.exp_pos _).le)
    (high_source_growth_ratio z hz N hN c hNm hn he)
  exact high_resource_local_affine z γ hz hs hγ hγmax Q Ω hQ N hN hlarge c hNm he

end ResourceLimitedCompetition
