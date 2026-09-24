import proofs.OverlappingSiphonInvasion.NormalizedBoundary
import proofs.OverlappingSiphonInvasion.BoundaryWeights
import proofs.OverlappingSiphonInvasion.FiberNeighborhood

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

def residentS1 (p : Rates) : ℝ := p.mu1/p.alpha1
def residentS2 (p : Rates) : ℝ := p.mu2/p.alpha2
def residentU1 (p : Rates) : ℝ := (p.recruitment-p.mu0*residentS1 p)/p.mu1
def residentU2 (p : Rates) : ℝ := (p.recruitment-p.mu0*residentS2 p)/p.mu2

/-- Strict invasion, expressed in the entries of the two source-derived
normal matrices. Resident existence and positivity of rates remain separate. -/
def StrictMutualInvasion (p : Rates) : Prop :=
  (0 ≤ p.alpha2*residentS1 p-p.gamma2*residentU1 p-p.mu2 ∨
    0 ≤ p.eta1*residentU1 p+p.alpha3*residentS1 p-p.mu3 ∨
    (p.alpha2*residentS1 p-p.gamma2*residentU1 p-p.mu2)*
      (p.eta1*residentU1 p+p.alpha3*residentS1 p-p.mu3) <
      (p.beta2*residentS1 p)*((p.gamma1+p.gamma2)*residentU1 p)) ∧
  (0 ≤ p.alpha1*residentS2 p-p.gamma1*residentU2 p-p.mu1 ∨
    0 ≤ p.eta2*residentU2 p+p.alpha3*residentS2 p-p.mu3 ∨
    (p.alpha1*residentS2 p-p.gamma1*residentU2 p-p.mu1)*
      (p.eta2*residentU2 p+p.alpha3*residentS2 p-p.mu3) <
      (p.beta1*residentS2 p)*((p.gamma1+p.gamma2)*residentU2 p))

private theorem resident_parameters (Λ α μ0 μ : ℝ)
    (hα : 0 < α) (hμ0 : 0 < μ0) (hμ : 0 < μ) (he : μ/α < Λ/μ0) :
    0 < μ/α ∧ 0 < (Λ-μ0*(μ/α))/μ ∧ α*(μ/α) = μ ∧ 0 < α*(Λ/μ0)-μ := by
  have hn : 0 < Λ-μ0*(μ/α) := by
    have hh := (lt_div_iff₀ hμ0).mp he
    nlinarith only [hh]
  have hh := (div_lt_iff₀ hα).mp he
  refine ⟨div_pos hμ hα,div_pos hn hμ,?_,by nlinarith only [hh]⟩
  field_simp

/-- Source-specific boundary growth: all rate and invasion assumptions are
the original strict ones. Every extinction trajectory eventually has a
positive relative-product growth margin, with no convergence hypothesis. -/
theorem source_boundary_eventual_growth (p : Rates) (hp : PositiveRates p)
    (he1 : p.mu1/p.alpha1 < p.recruitment/p.mu0)
    (he2 : p.mu2/p.alpha2 < p.recruitment/p.mu0) (hi : StrictMutualInvasion p) :
    ∃ ru rv rj : ℝ, ∃ k : ℕ, 0 < ru ∧ 0 < rv ∧ 0 < rj ∧ 0 < k ∧
      ∀ R : ℝ, 0 ≤ R → ∀ X : ℝ → LiftState,
        (∀ t, 0 ≤ t → X t ∈ physicalLiftClosure ru rv rj R) →
        (∀ t, 0 ≤ t → HasDerivAt X (normalizedField p ru rv rj (X t)) t) →
        extinctionProduct ru rv rj k (X 0) = 0 →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t in atTop, δ < normalGrowth p ru rv rj k (X t) := by
  have hΛ : 0 < p.recruitment := by simpa [rateVector] using hp 0
  have hα1 : 0 < p.alpha1 := by simpa [rateVector] using hp 1
  have hα2 : 0 < p.alpha2 := by simpa [rateVector] using hp 2
  have hμ0 : 0 < p.mu0 := by simpa [rateVector] using hp 10
  have hμ1 : 0 < p.mu1 := by simpa [rateVector] using hp 11
  have hμ2 : 0 < p.mu2 := by simpa [rateVector] using hp 12
  have hγ1 : 0 < p.gamma1 := by simpa [rateVector] using hp 6
  have hγ2 : 0 < p.gamma2 := by simpa [rateVector] using hp 7
  have hβ1 : 0 < p.beta1 := by simpa [rateVector] using hp 8
  have hβ2 : 0 < p.beta2 := by simpa [rateVector] using hp 9
  obtain ⟨hs1,hu1,hd1,ha⟩ := resident_parameters _ _ _ _ hα1 hμ0 hμ1 he1
  obtain ⟨hs2,hu2,hd2,hb⟩ := resident_parameters _ _ _ _ hα2 hμ0 hμ2 he2
  obtain ⟨ru,rv,rj,k,hru,hrv,hrj,hk,hfib⟩ := boundary_growth_weights p
    (p.recruitment/p.mu0) (residentS1 p) (residentU1 p) (residentS2 p) (residentU2 p)
    hu1 hu2 hd1 hd2 (mul_pos hβ2 hs1) (mul_pos (add_pos hγ1 hγ2) hu1) hi.1
    (mul_pos hβ1 hs2) (mul_pos (add_pos hγ1 hγ2) hu2) hi.2 ha hb
    (mul_pos (add_pos hβ1 hβ2) (div_pos hΛ hμ0))
  refine ⟨ru,rv,rj,k,hru,hrv,hrj,hk,?_⟩
  intro R hR X hX hd hP
  have hlim := normalized_boundary_projection_converges p hp ru rv rj R k
    hru hrv hrj hR he1 he2 X hX hd hP
  rcases hlim with h0 | h1 | h2
  · exact normalized_eventual_growth_of_projection_limit p ru rv rj R k hru hrv hrj
      X hX _ h0 (fun z hz he => hfib R z hz (Or.inl he))
  · exact normalized_eventual_growth_of_projection_limit p ru rv rj R k hru hrv hrj
      X hX _ h1 (fun z hz he => hfib R z hz (Or.inr (Or.inl he)))
  · exact normalized_eventual_growth_of_projection_limit p ru rv rj R k hru hrv hrj
      X hX _ h2 (fun z hz he => hfib R z hz (Or.inr (Or.inr he)))

end OverlappingSiphonInvasion
