import proofs.PowerLawSmallRAF.SeedClosed
import proofs.OverlapCorrectedRAF.Source.RepositorySemanticCounting
import Mathlib.Data.Nat.Choose.Sum

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source

/-- Probability of one particular subset when its cardinality has mass
`degreeMass` and the subset is uniform conditional on that cardinality. -/
noncomputable def subsetDegreeWeight {J : Type*} [Fintype J]
    (degreeMass : Nat → ℝ) (A : Finset J) : ℝ :=
  degreeMass A.card / Nat.choose (Fintype.card J) A.card

/-- Summing the uniform-conditional subset weights cancels the binomial
multiplicity in every cardinality fibre. -/
theorem sum_subsetDegreeWeight_eq_mass_sum
    {J : Type*} [Fintype J] [DecidableEq J]
    (degreeMass : Nat → ℝ) :
    (∑ A : Finset J, subsetDegreeWeight degreeMass A) =
      ∑ d ∈ Finset.range (Fintype.card J + 1), degreeMass d := by
  rw [← Finset.powerset_univ]
  simp only [subsetDegreeWeight]
  rw [Finset.sum_powerset_apply_card
    (fun d => degreeMass d / Nat.choose (Fintype.card J) d)]
  simp only [Finset.card_univ]
  apply Finset.sum_congr rfl
  intro d hd
  have hdJ : d ≤ Fintype.card J := by
    have hdlt := Finset.mem_range.mp hd
    omega
  have hchooseNat : 0 < Nat.choose (Fintype.card J) d :=
    Nat.choose_pos hdJ
  have hchoose : (Nat.choose (Fintype.card J) d : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  simp only [nsmul_eq_mul]
  field_simp

/-- One molecule's capped-Zipf/uniform-subset law is normalized.  The full
reaction subset has zero mass because the source degree is `min(K,R)-1`. -/
theorem sum_powerLawSubsetWeight_eq_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (a : ℝ) (ha : 1 < a) (hJ : 2 ≤ Fintype.card J) :
    (∑ A : Finset J,
      subsetDegreeWeight (cappedZipfDegreeMass a (Fintype.card J)) A) = 1 := by
  rw [sum_subsetDegreeWeight_eq_mass_sum]
  rw [Finset.sum_range_succ]
  have hfull : cappedZipfDegreeMass a (Fintype.card J) (Fintype.card J) = 0 := by
    simp [cappedZipfDegreeMass]
  rw [hfull, add_zero]
  exact cappedZipfDegreeMass_sum_eq_one a (Fintype.card J) ha hJ

/-- Molecule-oriented catalytic configuration: each molecule records exactly
the repository channels that it catalyzes. -/
abbrev RepositoryMoleculeFibreConfig (n : Nat) :=
  Molecule n → Finset (RepositoryChannel n)

/-- Product probability under independent molecule degree/subset draws. -/
noncomputable def repositoryPowerLawConfigWeight
    (a : ℝ) (n : Nat) (config : RepositoryMoleculeFibreConfig n) : ℝ :=
  ∏ x : Molecule n,
    subsetDegreeWeight
      (cappedZipfDegreeMass a (Fintype.card (RepositoryChannel n))) (config x)

/-- The independent product law on all molecule fibres is normalized. -/
theorem sum_repositoryPowerLawConfigWeight_eq_one
    (a : ℝ) (n : Nat) (ha : 1 < a)
    (hchannels : 2 ≤ Fintype.card (RepositoryChannel n)) :
    (∑ config : RepositoryMoleculeFibreConfig n,
      repositoryPowerLawConfigWeight a n config) = 1 := by
  simp only [repositoryPowerLawConfigWeight]
  rw [← Fintype.prod_sum]
  simp_rw [sum_powerLawSubsetWeight_eq_one a ha hchannels]
  simp

/-- Transpose a molecule-oriented incidence matrix into the channel-fibre
representation used by the overlap-corrected repository catalogue. -/
def channelFibreConfigOfMoleculeConfig (n : Nat)
    (config : RepositoryMoleculeFibreConfig n) :
    ∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) →
      Finset (Molecule n) :=
  fun r _ => Finset.univ.filter fun x => r ∈ config x

/-- Catalysis read from either orientation of the incidence matrix agrees
pointwise. -/
theorem repositoryCatalysisOf_transpose_apply
    (n : Nat) (config : RepositoryMoleculeFibreConfig n)
    (x : Molecule n) (r : RepositoryChannel n) :
    repositoryCatalysisOfFibreConfig
        (channelFibreConfigOfMoleculeConfig n config) x r ↔
      r ∈ config x := by
  simp [repositoryCatalysisOfFibreConfig,
    channelFibreConfigOfMoleculeConfig]

/-- The actual source-model RAF event, expressed on independent molecule
fibres. -/
noncomputable def repositoryPowerLawRAFConfigurations (n t : Nat) :
    Finset (RepositoryMoleculeFibreConfig n) :=
  Finset.univ.filter fun config =>
    channelFibreConfigOfMoleculeConfig n config ∈
      repositoryRAFFibreConfigurations n t

/-- Exact RAF probability for the source-faithful independent fixed-degree
fibre law. -/
noncomputable def repositoryPowerLawRAFProbability
    (a : ℝ) (n t : Nat) : ℝ :=
  ∑ config ∈ repositoryPowerLawRAFConfigurations n t,
    repositoryPowerLawConfigWeight a n config

/-- The new probability is literally the capped-Zipf product mass of the
existing exhaustive repository RAF partition, pulled back through incidence
matrix transposition. -/
theorem repositoryPowerLawRAFProbability_eq_repository_partition_mass
    (a : ℝ) (n t : Nat) :
    repositoryPowerLawRAFProbability a n t =
      ∑ config : RepositoryMoleculeFibreConfig n,
        if channelFibreConfigOfMoleculeConfig n config ∈
            repositoryRAFFibreConfigurations n t then
          repositoryPowerLawConfigWeight a n config
        else 0 := by
  rw [repositoryPowerLawRAFProbability,
    repositoryPowerLawRAFConfigurations]
  rw [Finset.sum_filter]

end PowerLawSmallRAF
