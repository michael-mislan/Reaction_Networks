import proofs.PowerLawSmallRAF.PowerLawFibreModel
import proofs.PowerLawSmallRAF.PairCoverage
import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source

theorem subsetDegreeWeight_nonneg
    {J : Type*} [Fintype J]
    (degreeMass : Nat → ℝ) (hmass : ∀ d, 0 ≤ degreeMass d)
    (A : Finset J) :
    0 ≤ subsetDegreeWeight degreeMass A := by
  exact div_nonneg (hmass A.card) (Nat.cast_nonneg _)

theorem repositoryPowerLawConfigWeight_nonneg
    (a : ℝ) (ha : 1 < a) (n : Nat)
    (config : RepositoryMoleculeFibreConfig n) :
    0 ≤ repositoryPowerLawConfigWeight a n config := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  apply Finset.prod_nonneg
  intro x hx
  exact subsetDegreeWeight_nonneg _
    (fun d => cappedZipfDegreeMass_nonneg a _ d hzpos) (config x)

/-- Molecule-oriented configurations in which some actual repository seed
channel is catalyzed. -/
noncomputable def repositoryPowerLawSeedOpenConfigurations (n : Nat) :
    Finset (RepositoryMoleculeFibreConfig n) :=
  Finset.univ.filter fun config =>
    ∃ seed ∈ repositorySeedChannels n 2, ∃ x, seed ∈ config x

noncomputable def repositoryPowerLawSeedOpenProbability
    (a : ℝ) (n : Nat) : ℝ :=
  ∑ config ∈ repositoryPowerLawSeedOpenConfigurations n,
    repositoryPowerLawConfigWeight a n config

/-- Exact one-molecule mass of avoiding a prescribed channel set. -/
noncomputable def finitePowerLawMoleculeMiss
    {J : Type*} [Fintype J] [DecidableEq J]
    (a : ℝ) (targets : Finset J) : ℝ :=
  ∑ A : Finset J,
    if Disjoint A targets then
      subsetDegreeWeight (cappedZipfDegreeMass a (Fintype.card J)) A
    else 0

theorem finitePowerLawMoleculeMiss_eq_gatewayMiss
    {J : Type*} [Fintype J] [DecidableEq J]
    (a : ℝ) (targets : Finset J) :
    finitePowerLawMoleculeMiss a targets =
      powerLawMoleculeGatewayMiss a (Fintype.card J) targets.card := by
  classical
  let N := Fintype.card J
  let C := N - targets.card
  have hcardCompl : targetsᶜ.card = C := by
    rw [Finset.card_compl]
  have hfilter :
      (Finset.univ.filter fun A : Finset J => Disjoint A targets) =
        targetsᶜ.powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powerset]
    exact Finset.subset_compl_iff_disjoint_right.symm
  rw [finitePowerLawMoleculeMiss, ← Finset.sum_filter, hfilter]
  simp only [subsetDegreeWeight]
  change (∑ A ∈ targetsᶜ.powerset,
    cappedZipfDegreeMass a N A.card / Nat.choose N A.card) = _
  rw [Finset.sum_powerset_apply_card
    (fun d => cappedZipfDegreeMass a N d / Nat.choose N d)]
  rw [hcardCompl]
  have hCN : C ≤ N := Nat.sub_le _ _
  let f : Nat → ℝ := fun d =>
    cappedZipfDegreeMass a N d *
      ((Nat.choose C d : ℝ) / Nat.choose N d)
  have hterms : ∀ d ∈ Finset.range (C + 1),
      Nat.choose C d •
          (cappedZipfDegreeMass a N d / Nat.choose N d) = f d := by
    intro d hd
    have hdC : d ≤ C := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have hdN : d ≤ N := hdC.trans hCN
    have hchoose : (Nat.choose N d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hdN).ne'
    simp only [nsmul_eq_mul, f]
    field_simp
  rw [Finset.sum_congr rfl hterms]
  have hextend :
      (∑ d ∈ Finset.range (C + 1), f d) =
        ∑ d ∈ Finset.range (N + 1), f d := by
    apply Finset.sum_subset
    · exact Finset.range_mono (Nat.succ_le_succ hCN)
    · intro d hdN hdnotC
      have hdC : C < d := by
        simpa only [Finset.mem_range, not_lt] using hdnotC
      simp [f, Nat.choose_eq_zero_of_lt hdC]
  rw [hextend, Finset.sum_range_succ]
  have hfull : cappedZipfDegreeMass a N N = 0 := by
    simp [cappedZipfDegreeMass]
  rw [show f N = 0 by simp [f, hfull], add_zero]
  change (∑ d ∈ Finset.range N,
      cappedZipfDegreeMass a N d *
        ((Nat.choose (N - targets.card) d : ℝ) / Nat.choose N d)) = _
  rfl

/-- Product mass of configurations in which every molecule avoids every
actual repository seed channel. -/
noncomputable def repositoryPowerLawSeedClosedProbability
    (a : ℝ) (n : Nat) : ℝ :=
  ∑ config : RepositoryMoleculeFibreConfig n,
    if ∀ x, Disjoint (config x) (repositorySeedChannels n 2) then
      repositoryPowerLawConfigWeight a n config
    else 0

theorem repositoryPowerLawSeedClosedProbability_exact
    (a : ℝ) (n : Nat) :
    repositoryPowerLawSeedClosedProbability a n =
      (finitePowerLawMoleculeMiss a (repositorySeedChannels n 2)) ^
        Fintype.card (Molecule n) := by
  classical
  rw [repositoryPowerLawSeedClosedProbability]
  simp only [repositoryPowerLawConfigWeight]
  have hpoint : ∀ config : RepositoryMoleculeFibreConfig n,
      (if ∀ x, Disjoint (config x) (repositorySeedChannels n 2) then
          ∏ x, subsetDegreeWeight
            (cappedZipfDegreeMass a (Fintype.card (RepositoryChannel n)))
            (config x)
        else 0) =
      ∏ x, if Disjoint (config x) (repositorySeedChannels n 2) then
          subsetDegreeWeight
            (cappedZipfDegreeMass a (Fintype.card (RepositoryChannel n)))
            (config x)
        else 0 := by
    intro config
    by_cases h : ∀ x, Disjoint (config x) (repositorySeedChannels n 2)
    · simp [h]
    · simp only [if_neg h]
      push Not at h
      obtain ⟨x, hx⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ x)]
      simp [hx]
  simp_rw [hpoint]
  rw [← Fintype.prod_sum (fun _ A =>
    if Disjoint A (repositorySeedChannels n 2) then
      subsetDegreeWeight
        (cappedZipfDegreeMass a (Fintype.card (RepositoryChannel n))) A
    else 0)]
  simp only [finitePowerLawMoleculeMiss]
  simp

theorem repositoryPowerLawSeedOpenProbability_eq_one_sub_closed
    (a : ℝ) (ha : 1 < a) (n : Nat)
    (hchannels : 2 ≤ Fintype.card (RepositoryChannel n)) :
    repositoryPowerLawSeedOpenProbability a n =
      1 - repositoryPowerLawSeedClosedProbability a n := by
  classical
  let openEvent : RepositoryMoleculeFibreConfig n → Prop := fun config =>
    ∃ seed ∈ repositorySeedChannels n 2, ∃ x, seed ∈ config x
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (RepositoryMoleculeFibreConfig n)) openEvent
    (repositoryPowerLawConfigWeight a n)
  have hclosed :
      (∑ config ∈ (Finset.univ : Finset (RepositoryMoleculeFibreConfig n)).filter
          (fun config => ¬ openEvent config),
          repositoryPowerLawConfigWeight a n config) =
        repositoryPowerLawSeedClosedProbability a n := by
    rw [repositoryPowerLawSeedClosedProbability]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro config _hconfig
    by_cases hopen : openEvent config
    · have hnotdisjoint : ¬ ∀ x,
          Disjoint (config x) (repositorySeedChannels n 2) := by
        intro hall
        obtain ⟨seed, hseedTarget, x, hseedConfig⟩ := hopen
        exact (Finset.disjoint_left.mp (hall x)) hseedConfig hseedTarget
      simp [hopen, hnotdisjoint]
    · have hdisjoint : ∀ x,
          Disjoint (config x) (repositorySeedChannels n 2) := by
        intro x
        rw [Finset.disjoint_left]
        intro seed hseedConfig hseedTarget
        exact hopen ⟨seed, hseedTarget, x, hseedConfig⟩
      simp [hopen, hdisjoint]
  have htotal := sum_repositoryPowerLawConfigWeight_eq_one a n ha hchannels
  rw [repositoryPowerLawSeedOpenProbability,
    repositoryPowerLawSeedOpenConfigurations]
  change (∑ config ∈ (Finset.univ : Finset (RepositoryMoleculeFibreConfig n)).filter
      openEvent, repositoryPowerLawConfigWeight a n config) = _
  rw [← hclosed]
  linarith

theorem repositoryPowerLawSeedOpenProbability_exact
    (a : ℝ) (ha : 1 < a) (n : Nat)
    (hchannels : 2 ≤ Fintype.card (RepositoryChannel n)) :
    repositoryPowerLawSeedOpenProbability a n =
      1 - (finitePowerLawMoleculeMiss a (repositorySeedChannels n 2)) ^
        Fintype.card (Molecule n) := by
  rw [repositoryPowerLawSeedOpenProbability_eq_one_sub_closed a ha n hchannels,
    repositoryPowerLawSeedClosedProbability_exact]

theorem repositoryPowerLaw_raf_implies_seedOpen
    (n : Nat) (config : RepositoryMoleculeFibreConfig n)
    (hconfig : channelFibreConfigOfMoleculeConfig n config ∈
      repositoryRAFFibreConfigurations n 2) :
    ∃ seed ∈ repositorySeedChannels n 2, ∃ x, seed ∈ config x := by
  classical
  have hexists : ∃ S : Finset (RepositoryChannel n),
      IsRevRAF (repositoryCRS n 2)
        (repositoryCatalysisOfFibreConfig
          (channelFibreConfigOfMoleculeConfig n config)) S := by
    simpa [repositoryRAFFibreConfigurations] using hconfig
  obtain ⟨S, hraf⟩ := hexists
  obtain ⟨seed, hseed, x, hx⟩ :=
    repository_raf_has_catalyzed_gateway n 2
      (repositoryCatalysisOfFibreConfig
        (channelFibreConfigOfMoleculeConfig n config)) S hraf
  refine ⟨seed, ?_, x, ?_⟩
  · simp [repositorySeedChannels, hseed]
  · exact (repositoryCatalysisOf_transpose_apply n config x seed).mp hx

theorem repositoryPowerLawRAFProbability_le_seedOpen
    (a : ℝ) (ha : 1 < a) (n : Nat) :
    repositoryPowerLawRAFProbability a n 2 ≤
      repositoryPowerLawSeedOpenProbability a n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro config hconfig
    rw [repositoryPowerLawRAFConfigurations, Finset.mem_filter] at hconfig
    rw [repositoryPowerLawSeedOpenConfigurations, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      repositoryPowerLaw_raf_implies_seedOpen n config hconfig.2⟩
  · exact fun config _ _ => repositoryPowerLawConfigWeight_nonneg a ha n config

/-- Source-faithful replacement for the Bernoulli gateway bound: the actual
repository RAF event is bounded by the exact capped-Zipf seed-open law. -/
theorem repositoryPowerLawRAFProbability_le_exact_seed_open
    (a : ℝ) (ha : 1 < a) (n : Nat)
    (hchannels : 2 ≤ Fintype.card (RepositoryChannel n)) :
    repositoryPowerLawRAFProbability a n 2 ≤
      1 - powerLawSeedClosedProbability a
        (Fintype.card (RepositoryChannel n))
        (repositorySeedChannels n 2).card
        (Fintype.card (Molecule n)) := by
  calc
    repositoryPowerLawRAFProbability a n 2 ≤
        repositoryPowerLawSeedOpenProbability a n :=
      repositoryPowerLawRAFProbability_le_seedOpen a ha n
    _ = 1 - (finitePowerLawMoleculeMiss a (repositorySeedChannels n 2)) ^
          Fintype.card (Molecule n) :=
      repositoryPowerLawSeedOpenProbability_exact a ha n hchannels
    _ = 1 - powerLawSeedClosedProbability a
          (Fintype.card (RepositoryChannel n))
          (repositorySeedChannels n 2).card
          (Fintype.card (Molecule n)) := by
      rw [finitePowerLawMoleculeMiss_eq_gatewayMiss]
      rfl

/-- PL36 docking theorem.  It packages the exact source-law emergence bound
with the six-coordinate sufficiency theorem for the overlap correction, so no
Bernoulli or global-fixed-`Q` stochastic assumption is imported. -/
theorem powerLawOverlapCorrectedEmergenceDock
    {R : Type*} [Fintype R] [DecidableEq R]
    (a : ℝ) (ha : 1 < a) (n : Nat)
    (hchannels : 2 ≤ Fintype.card (RepositoryChannel n))
    (u : Nat → ℝ) (S T S' T' : Finset R) (q q' v : Nat)
    (hS : S.card = S'.card) (hT : T.card = T'.card)
    (hI : (S ∩ T).card = (S' ∩ T').card) :
    repositoryPowerLawRAFProbability a n 2 ≤
        1 - powerLawSeedClosedProbability a
          (Fintype.card (RepositoryChannel n))
          (repositorySeedChannels n 2).card
          (Fintype.card (Molecule n)) ∧
      pairCoverageKernel u S T q q' v =
        pairCoverageKernel u S' T' q q' v := by
  exact ⟨repositoryPowerLawRAFProbability_le_exact_seed_open
      a ha n hchannels,
    pairCoverageKernel_eq_of_coordinates u S T S' T' q q' v hS hT hI⟩

end PowerLawSmallRAF
