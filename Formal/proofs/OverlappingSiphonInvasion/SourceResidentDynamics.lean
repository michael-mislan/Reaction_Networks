import proofs.OverlappingSiphonInvasion.ResidentDynamics
import proofs.OverlappingSiphonInvasion.ResidentInvasion

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

private theorem canonical_resident_converges (Λ α μ₀ μ : ℝ) (s u : ℝ → ℝ)
    (hΛ : 0 < Λ) (hα : 0 < α) (hμ₀ : 0 < μ₀) (hμ : 0 < μ)
    (he : μ/α < Λ/μ₀)
    (hpos : ∀ t, 0 ≤ t → 0 < s t ∧ 0 < u t)
    (hds : ∀ t, 0 ≤ t → HasDerivAt s (Λ-μ₀*s t-α*s t*u t) t)
    (hdu : ∀ t, 0 ≤ t → HasDerivAt u (u t*(α*s t-μ)) t) :
    Tendsto s atTop (𝓝 (μ/α)) ∧ Tendsto u atTop (𝓝 ((Λ-μ₀*(μ/α))/μ)) := by
  have hn : 0 < Λ-μ₀*(μ/α) := by
    have hh := (lt_div_iff₀ hμ₀).mp he
    nlinarith only [hh]
  apply resident_positive_converges Λ α μ₀ μ (μ/α) ((Λ-μ₀*(μ/α))/μ) s u
    hΛ hα hμ₀ hμ (div_pos hμ hα) (div_pos hn hμ) _ _ hpos hds hdu
  · field_simp
    ring
  · field_simp

/-- Boundary resident convergence is tied to the literal reaction source,
with equilibrium existence expressed solely in the original rate parameters. -/
theorem source_resident1_converges (p : Rates) (hp : PositiveRates p)
    (he : p.mu1/p.alpha1 < p.recruitment/p.mu0) (s u : ℝ → ℝ)
    (hpos : ∀ t, 0 ≤ t → 0 < s t ∧ 0 < u t)
    (hds : ∀ t, 0 ≤ t → HasDerivAt s
      (source.massAction (rateVector p) (face1 (s t) (u t)) 0) t)
    (hdu : ∀ t, 0 ≤ t → HasDerivAt u
      (source.massAction (rateVector p) (face1 (s t) (u t)) 1) t) :
    Tendsto s atTop (𝓝 (p.mu1/p.alpha1)) ∧
      Tendsto u atTop (𝓝 ((p.recruitment-p.mu0*(p.mu1/p.alpha1))/p.mu1)) := by
  apply canonical_resident_converges p.recruitment p.alpha1 p.mu0 p.mu1 s u
    (by simpa [rateVector] using hp 0) (by simpa [rateVector] using hp 1)
    (by simpa [rateVector] using hp 10) (by simpa [rateVector] using hp 11) he hpos
  · intro t ht
    convert hds t ht using 1
    simp [source_field,field,face1]
    ring
  · intro t ht
    simpa [source_field,field,face1] using hdu t ht

theorem source_resident2_converges (p : Rates) (hp : PositiveRates p)
    (he : p.mu2/p.alpha2 < p.recruitment/p.mu0) (s u : ℝ → ℝ)
    (hpos : ∀ t, 0 ≤ t → 0 < s t ∧ 0 < u t)
    (hds : ∀ t, 0 ≤ t → HasDerivAt s
      (source.massAction (rateVector p) (face2 (s t) (u t)) 0) t)
    (hdu : ∀ t, 0 ≤ t → HasDerivAt u
      (source.massAction (rateVector p) (face2 (s t) (u t)) 2) t) :
    Tendsto s atTop (𝓝 (p.mu2/p.alpha2)) ∧
      Tendsto u atTop (𝓝 ((p.recruitment-p.mu0*(p.mu2/p.alpha2))/p.mu2)) := by
  apply canonical_resident_converges p.recruitment p.alpha2 p.mu0 p.mu2 s u
    (by simpa [rateVector] using hp 0) (by simpa [rateVector] using hp 2)
    (by simpa [rateVector] using hp 10) (by simpa [rateVector] using hp 12) he hpos
  · intro t ht
    convert hds t ht using 1
    simp [source_field,field,face2]
    ring
  · intro t ht
    simpa [source_field,field,face2] using hdu t ht

theorem source_diseaseFree_converges (p : Rates) (hp : PositiveRates p) (s : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt s
      (source.massAction (rateVector p) (face1 (s t) 0) 0) t) :
    Tendsto s atTop (𝓝 (p.recruitment/p.mu0)) := by
  apply diseaseFree_converges p.recruitment p.mu0 s
    (by simpa [rateVector] using hp 10)
  intro t ht
  simpa [source_field,field,face1,mul_comm] using hd t ht

end OverlappingSiphonInvasion
