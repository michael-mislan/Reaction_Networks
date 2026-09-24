import proofs.HeritableCompositions.SourceAffine
import proofs.HeritableCompositions.SourceClockRates
import proofs.HeritableCompositions.PartitionFailure

namespace HeritableCompositions
open FiniteCopy CoreCouplingCAC Set

/-- Algebraic conditions on the literal reaction generator; no small-error
probability or birth-kernel assumption is a field of this certificate. -/
structure GrowthCertificate (γ : ℝ) where
  center : Point
  energy : Point → ℝ
  center_upper : ∀ i, center i ≤ 34
  energy_lower : ∀ y, (1/200)*normSq y ≤ energy y
  return_bound : ∀ (y v : Point), energy y ≤ 2*innerEnergy → (∀ i, |v i| ≤ 1/1000000) →
    energy (fun i => y i+v i) < 4*innerEnergy
  ceiling : ∀ (N : ℕ), 1 ≤ N → ∀ (c : Compartment), N ≤ c.2 →
    energy (fun i => concentration c.2 c.1 i-center i) < outerEnergy →
    compartmentGenerator γ (fun d => Real.exp ((N : ℝ)*localAlpha*energy (fun i => concentration d.2 d.1 i-center i))) c ≤
      growingCeiling N γ
  affine : ∀ (N : ℕ), 1 ≤ N → (140000000000000000000 : ℝ) ≤ N → ∀ (c : Compartment), N ≤ c.2 →
    energy (fun i => concentration c.2 c.1 i-center i) < outerEnergy →
    compartmentGenerator γ (fun d => Real.exp ((N : ℝ)*localAlpha*energy (fun i => concentration d.2 d.1 i-center i))) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*Real.exp ((N : ℝ)*localAlpha*energy (fun i => concentration c.2 c.1 i-center i))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2))
  rates : ∀ (N : ℕ), 1 ≤ N → ∀ (b : ℝ), b ≤ outerEnergy → ∀ c ∈ growthDomain N center energy b,
    (γ*(99/100))*(N : ℝ) ≤ γ*(c.1 2 : ℝ) ∧ γ*(c.1 2 : ℝ) ≤ 2*(γ*4)*(N : ℝ)

noncomputable def lowCertificate (z γ : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) : GrowthCertificate γ := {
  center := pointOfState (lift sourceRates z)
  energy := lowEnergy
  center_upper := lowroot_upper z hz
  energy_lower := lowEnergy_lower
  return_bound := low_partition_return
  ceiling := fun N hN c hNm he => low_growth_local_ceiling z γ hz hstationary hγ hγmax N hN c hNm he
  affine := fun N hN hlarge c hNm he => low_growth_local_affine z γ hz hstationary hγ hγmax N hN hlarge c hNm he
  rates := by
    intro N hN b hb c hc
    have h := low_domain_membrane_rates z γ hz hγ N hN b hb c hc
    have hp : 0 ≤ γ*(N : ℝ) := mul_nonneg hγ (Nat.cast_nonneg N)
    exact ⟨h.1,by nlinarith only [h.2,hp]⟩ }

noncomputable def highCertificate (z γ : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hstationary : Stationary sourceRates (lift sourceRates z))
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000) : GrowthCertificate γ := {
  center := pointOfState (lift sourceRates z)
  energy := highEnergy
  center_upper := highroot_upper z hz
  energy_lower := highEnergy_lower
  return_bound := high_partition_return
  ceiling := fun N hN c hNm he => high_growth_local_ceiling z γ hz hstationary hγ hγmax N hN c hNm he
  affine := fun N hN hlarge c hNm he => high_growth_local_affine z γ hz hstationary hγ hγmax N hN hlarge c hNm he
  rates := by
    intro N hN b hb c hc
    have h := high_domain_membrane_rates z γ hz hγ N hN b hb c hc
    have hp : 0 ≤ γ*(N : ℝ) := mul_nonneg hγ (Nat.cast_nonneg N)
    constructor <;> nlinarith only [h.1,h.2,hp] }

end HeritableCompositions
