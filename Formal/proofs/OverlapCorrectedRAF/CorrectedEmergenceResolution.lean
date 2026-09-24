import proofs.OverlapCorrectedRAF.Overlap.Nonoverlap
import proofs.OverlapCorrectedRAF.Asymptotic.SublinearCatalysis
import proofs.OverlapCorrectedRAF.Source.RepositorySemanticCounting

namespace OverlapCorrectedRAF

open Filter Topology
open RAF RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source

/-- The two exact finite probability interfaces, specialized to the literal
repository molecule and reversible-channel types.  The core index `K` carries
the finite catalogue; `requirements k j` is the food-closure molecule set
eligible to hit channel `j` for core `k`, with `∅` denoting an unused channel. -/
def HasExactFiniteOverlapLaw
    {K : Type*} [DecidableEq K]
    (n Q : Nat) (expectedCatalysis : ℝ) (cores : Finset K)
    (requirements : K → RepositoryChannel n → Finset (Molecule n)) : Prop :=
  (Overlap.rafBernoulliProbability
      (Asymptotic.repositoryCatalysisP expectedCatalysis n)
      (Finset.univ : Finset (RepositoryChannel n)) cores requirements =
    ∑ selected ∈ cores.powerset,
      if selected.Nonempty then
        (-1 : ℝ) ^ (selected.card + 1) *
          Overlap.jointBernoulliHitProbability
            (Asymptotic.repositoryCatalysisP expectedCatalysis n)
            (Finset.univ : Finset (RepositoryChannel n)) requirements selected
      else 0) ∧
  (Overlap.rafFixedQProbability
      (Finset.univ : Finset (RepositoryChannel n)) cores requirements Q =
    Int.toNat ((∑ selected ∈ cores.powerset,
      if selected.Nonempty then
        Polynomial.C ((-1 : Int) ^ (selected.card + 1)) *
          Overlap.jointFixedQHitPolynomial
            (Finset.univ : Finset (RepositoryChannel n)) requirements selected
      else 0).coeff Q) /
      Nat.choose
        (Fintype.card (Molecule n) *
          (Finset.univ : Finset (RepositoryChannel n)).card) Q)

theorem hasExactFiniteOverlapLaw
    {K : Type*} [DecidableEq K]
    (n Q : Nat) (expectedCatalysis : ℝ) (cores : Finset K)
    (requirements : K → RepositoryChannel n → Finset (Molecule n)) :
    HasExactFiniteOverlapLaw n Q expectedCatalysis cores requirements := by
  constructor
  · exact Overlap.rafBernoulliProbability_exact
      (Asymptotic.repositoryCatalysisP expectedCatalysis n)
      (Finset.univ : Finset (RepositoryChannel n)) cores requirements
  · exact Overlap.rafFixedQProbability_exact
      (Finset.univ : Finset (RepositoryChannel n)) cores requirements Q

/-- The exact finite laws specialized to the exhaustive catalogue of actual
repository RAF supports.  Both right-hand sides are literal measures of
configurations for which `IsRevRAF` holds for some nonempty support. -/
def HasExactRepositoryRAFLaw
    (n t Q : Nat) (expectedCatalysis : ℝ) : Prop :=
  (Overlap.rafBernoulliProbability
      (Asymptotic.repositoryCatalysisP expectedCatalysis n)
      (Finset.univ : Finset (RepositoryChannel n))
      (Source.repositoryCoreSupports n t)
      (Source.repositorySupportRequirements n t) =
    ∑ config ∈ Source.repositoryRAFFibreConfigurations n t,
      Overlap.jointFibreBernoulliWeight
        (Asymptotic.repositoryCatalysisP expectedCatalysis n)
        (Finset.univ : Finset (RepositoryChannel n)) config) ∧
  (Overlap.rafFixedQProbability
      (Finset.univ : Finset (RepositoryChannel n))
      (Source.repositoryCoreSupports n t)
      (Source.repositorySupportRequirements n t) Q =
    ((Source.repositoryRAFFibreConfigurations n t).filter fun config =>
        (∑ r ∈ (Finset.univ : Finset (RepositoryChannel n)).attach,
          (config r.1 r.2).card) = Q).card /
      Nat.choose (Fintype.card (Molecule n) *
        Fintype.card (RepositoryChannel n)) Q)

theorem hasExactRepositoryRAFLaw
    (n t Q : Nat) (expectedCatalysis : ℝ) :
    HasExactRepositoryRAFLaw n t Q expectedCatalysis := by
  exact ⟨Source.repository_rafBernoulliProbability_eq_actual_raf_mass
      (Asymptotic.repositoryCatalysisP expectedCatalysis n) n t,
    Source.repository_rafFixedQProbability_eq_actual_raf_ratio n t Q⟩

/-- Source-faithful corrected emergence resolution.

It combines: (i) the exact finite overlap partition on the repository's actual
molecule--reversible-channel coordinates, (ii) deterministic necessity of a
catalysed source gateway for every repository RAF, and (iii) the quantitative
negative replacement for the apparent constant-`f` transition: every
sublinear expected-catalysis scale has vanishing RAF probability. -/
theorem correctedEmergenceResolution
    (n t Q : Nat) (expectedCatalysis : ℝ)
    (C : RepositoryCatalysis n) (S : Finset (RepositoryChannel n))
    (hraf : IsRevRAF (repositoryCRS n t) C S)
    (f : Nat → ℝ)
    (hf : ∀ m, 0 ≤ f m)
    (hfChannels : ∀ m, f m ≤ Fintype.card (RepositoryChannel m))
    (hsublinear : Tendsto (fun m => f m / (m : ℝ)) atTop (𝓝 0)) :
    HasExactRepositoryRAFLaw n t Q expectedCatalysis ∧
      (∃ r : RepositoryChannel n,
        RevSeedReaction (repositoryCRS n t) r ∧ ∃ x : Molecule n, C x r) ∧
      Tendsto (Asymptotic.repositoryRAFBernoulliProbability f)
        atTop (𝓝 0) := by
  refine ⟨hasExactRepositoryRAFLaw n t Q expectedCatalysis,
    repository_raf_has_catalyzed_gateway n t C S hraf, ?_⟩
  exact Asymptotic.sublinear_catalysis_forces_actual_repository_raf_vanishing
    f hf hfChannels hsublinear

end OverlapCorrectedRAF
