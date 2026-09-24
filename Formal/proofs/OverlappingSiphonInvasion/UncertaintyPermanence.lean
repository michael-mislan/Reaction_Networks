import proofs.OverlappingSiphonInvasion.PublicationEndpoint
import proofs.OverlappingSiphonInvasion.PublicationCertificates

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

theorem one_percent_permanence (p : Rates) (hb : OnePercentBox p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ X : ℝ → State, IsTrajectory p X →
      ∀ᶠ t in atTop, ∀ i, ε ≤ X t i ∧ X t i ≤ p.recruitment/deathFloor p+1 := by
  obtain ⟨hp,he1,he2,h11,h12,h21,h22⟩ := one_percent_mutual_invasion p hb
  have hα1 : 0 < p.alpha1 := hp 1
  have hα2 : 0 < p.alpha2 := hp 2
  have hγ1 : 0 < p.gamma1 := hp 6
  have hγ2 : 0 < p.gamma2 := hp 7
  have hβ1 : 0 < p.beta1 := hp 8
  have hβ2 : 0 < p.beta2 := hp 9
  have hμ0 : 0 < p.mu0 := hp 10
  have hμ1 : 0 < p.mu1 := hp 11
  have hμ2 : 0 < p.mu2 := hp 12
  have hs1 : 0 < residentS1 p := div_pos hμ1 hα1
  have hs2 : 0 < residentS2 p := div_pos hμ2 hα2
  have hu1 : 0 < residentU1 p := by
    have hh := (lt_div_iff₀ hμ0).mp he1
    apply div_pos _ hμ1
    dsimp [residentS1]
    linarith
  have hu2 : 0 < residentU2 p := by
    have hh := (lt_div_iff₀ hμ0).mp he2
    apply div_pos _ hμ2
    dsimp [residentS2]
    linarith
  have hi : StrictMutualInvasion p := by
    constructor
    · apply (positive_covector_iff _ _ _ _ (mul_pos hβ2 hs1)
        (mul_pos (add_pos hγ1 hγ2) hu1)).mp
      refine ⟨2,by norm_num,?_,?_⟩
      · dsimp [residentS1,residentU1] at *
        nlinarith only [h11]
      · dsimp [residentS1,residentU1] at *
        nlinarith only [h12]
    · apply (positive_covector_iff _ _ _ _ (mul_pos hβ1 hs2)
        (mul_pos (add_pos hγ1 hγ2) hu2)).mp
      refine ⟨1,by norm_num,?_,?_⟩
      · dsimp [residentS2,residentU2] at *
        nlinarith only [h21]
      · dsimp [residentS2,residentU2] at *
        nlinarith only [h22]
  exact general_trajectory_permanence p hp he1 he2 hi

end OverlappingSiphonInvasion
