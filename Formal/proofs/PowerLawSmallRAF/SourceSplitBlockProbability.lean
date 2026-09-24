import proofs.PowerLawSmallRAF.SourceSplitBlocks

namespace PowerLawSmallRAF

open Filter Topology
open RAF RAF.Polymer RAF.Concrete

theorem powerLawCoverageMissProfile_zero
    (a : ℝ) (ha : 1 < a) (R : Nat) (hR : 2 ≤ R) :
    coverageMissProfile (cappedZipfDegreeMass a R) R 0 = 1 := by
  rw [powerLawCoverageMissProfile_eq]
  have hpoint : ∀ d ∈ Finset.range R,
      hypergeometricGatewayMiss R 0 d = 1 := by
    intro d hd
    have hchoose : (Nat.choose R d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (Finset.mem_range.mp hd).le))
    simp only [hypergeometricGatewayMiss, Nat.sub_zero]
    exact div_self hchoose
  rw [powerLawMoleculeGatewayMiss]
  calc
    (∑ d ∈ Finset.range R,
      cappedZipfDegreeMass a R d * hypergeometricGatewayMiss R 0 d) =
        ∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hpoint d hd, mul_one]
    _ = 1 := cappedZipfDegreeMass_sum_eq_one a R ha hR

/-- Source configurations in which every catalyst fibre misses one product
split block. -/
def sourceSplitBlockMissEvent {n : Nat} (x : Molecule n) :
    Finset (SourceMoleculeFibreConfig n) :=
  Finset.univ.filter fun config =>
    ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x)

/-- Total source mass on which every block indexed by `B` is hit at least
once.  `B` is the finite-window version of the PL58 macro core. -/
noncomputable def sourceSplitBlocksCoveredWeight {n : Nat}
    (a : ℝ) (B : Finset (Molecule n)) : ℝ :=
  allCoveredWeight B sourceSplitBlockMissEvent
    (sourcePowerLawConfigWeight a n)

theorem mem_sourceSplitBlockMissEvent_iff {n : Nat}
    (x : Molecule n) (config : SourceMoleculeFibreConfig n) :
    config ∈ sourceSplitBlockMissEvent x ↔
      ∀ y : Molecule n, Disjoint (config y) (sourceSplitBlock x) := by
  simp [sourceSplitBlockMissEvent]

theorem mem_inf_sourceSplitBlockMissEvent_iff {n : Nat}
    (T : Finset (Molecule n)) (config : SourceMoleculeFibreConfig n) :
    config ∈ T.inf sourceSplitBlockMissEvent ↔
      ∀ y : Molecule n,
        Disjoint (config y) (T.biUnion sourceSplitBlock) := by
  simp only [Finset.mem_inf, mem_sourceSplitBlockMissEvent_iff,
    Finset.disjoint_left, Finset.mem_biUnion]
  constructor
  · intro h y r hry hr
    obtain ⟨x, hxT, hrx⟩ := hr
    exact h x hxT y hry hrx
  · intro h x hxT y r hry hrx
    exact h y hry ⟨x, hxT, hrx⟩

/-- Exact finite-block inclusion-exclusion under the literal source product
law.  No independence between reaction coordinates is assumed. -/
theorem sourceSplitBlocksCoveredWeight_eq {n : Nat}
    (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) (B : Finset (Molecule n)) :
    sourceSplitBlocksCoveredWeight a B =
      ∑ T ∈ B.powerset,
        (-1 : ℝ) ^ T.card *
          coverageMissProfile
              (cappedZipfDegreeMass a (sourceReactionCount n))
              (sourceReactionCount n) (T.biUnion sourceSplitBlock).card ^
            sourceMoleculeCount n := by
  rw [sourceSplitBlocksCoveredWeight, allCoveredWeight,
    Finset.inclusion_exclusion_sum_inf_compl]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 1
  have hcard : (Finset.univ : Finset (Molecule n)).card =
      sourceMoleculeCount n := by
    rw [Finset.card_univ, card_binaryMolecule_eq_sourceMoleculeCount]
  have hinf : T.inf sourceSplitBlockMissEvent =
      (Finset.univ : Finset (SourceMoleculeFibreConfig n)).filter
        (fun config => ∀ y : Molecule n,
          Disjoint (config y) (T.biUnion sourceSplitBlock)) := by
    ext config
    simp [mem_inf_sourceSplitBlockMissEvent_iff]
  rw [hinf, Finset.sum_filter]
  have hevent (config : SourceMoleculeFibreConfig n) :
      (∀ y : Molecule n,
        Disjoint (config y) (T.biUnion sourceSplitBlock)) ↔
      (∀ y : ↥(Finset.univ : Finset (Molecule n)),
        Disjoint (config y) (T.biUnion sourceSplitBlock)) := by
    constructor
    · intro h y
      exact h y
    · intro h y
      exact h ⟨y, Finset.mem_univ y⟩
  simp_rw [hevent]
  rw [source_jointMiss_mass_eq_pow a ha hn
    (Finset.univ : Finset (Molecule n))
    (T.biUnion sourceSplitBlock), hcard]

/-- Indexed version used to transport one fixed finite word window through
the growing source cutoff. -/
def sourceIndexedBlockMissEvent {I : Type*} {n : Nat}
    (block : I → Finset (Reaction n)) (i : I) :
    Finset (SourceMoleculeFibreConfig n) :=
  Finset.univ.filter fun config =>
    ∀ y : Molecule n, Disjoint (config y) (block i)

noncomputable def sourceIndexedBlocksCoveredWeight
    {I : Type*} [Fintype I] [DecidableEq I] {n : Nat}
    (a : ℝ) (block : I → Finset (Reaction n)) : ℝ :=
  allCoveredWeight Finset.univ (sourceIndexedBlockMissEvent block)
    (sourcePowerLawConfigWeight a n)

theorem sourceIndexedBlocksCoveredWeight_eq
    {I : Type*} [Fintype I] [DecidableEq I] {n : Nat}
    (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (block : I → Finset (Reaction n)) :
    sourceIndexedBlocksCoveredWeight a block =
      ∑ T ∈ (Finset.univ : Finset I).powerset,
        (-1 : ℝ) ^ T.card *
          coverageMissProfile
              (cappedZipfDegreeMass a (sourceReactionCount n))
              (sourceReactionCount n) (T.biUnion block).card ^
            sourceMoleculeCount n := by
  rw [sourceIndexedBlocksCoveredWeight, allCoveredWeight,
    Finset.inclusion_exclusion_sum_inf_compl]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 1
  have hcard : (Finset.univ : Finset (Molecule n)).card =
      sourceMoleculeCount n := by
    rw [Finset.card_univ, card_binaryMolecule_eq_sourceMoleculeCount]
  have hinf : T.inf (sourceIndexedBlockMissEvent block) =
      (Finset.univ : Finset (SourceMoleculeFibreConfig n)).filter
        (fun config => ∀ y : Molecule n,
          Disjoint (config y) (T.biUnion block)) := by
    ext config
    simp only [Finset.mem_inf, sourceIndexedBlockMissEvent,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left,
      Finset.mem_biUnion]
    constructor
    · intro h y r hry hr
      obtain ⟨i, hiT, hri⟩ := hr
      exact h i hiT y hry hri
    · intro h i hiT y r hry hri
      exact h y hry ⟨i, hiT, hri⟩
  rw [hinf, Finset.sum_filter]
  have hevent (config : SourceMoleculeFibreConfig n) :
      (∀ y : Molecule n, Disjoint (config y) (T.biUnion block)) ↔
      (∀ y : ↥(Finset.univ : Finset (Molecule n)),
        Disjoint (config y) (T.biUnion block)) := by
    constructor
    · intro h y
      exact h y
    · intro h y
      exact h ⟨y, Finset.mem_univ y⟩
  simp_rw [hevent]
  rw [source_jointMiss_mass_eq_pow a ha hn
    (Finset.univ : Finset (Molecule n)) (T.biUnion block), hcard]

/-- Every fixed finite family of disjoint-sized source blocks has the Poisson
occupancy limit dictated only by the block union cardinalities.  The block
identities may move with `n`; only their exact union sizes are fixed. -/
theorem calibrated_sourceIndexedBlocksCoveredWeight_tendsto
    {I : Type*} [Fintype I] [DecidableEq I]
    (lam : ℝ) (hlam : 0 < lam)
    (block : ∀ n : Nat, I → Finset (Reaction n)) (blockSize : I → Nat)
    (hcard : ∀ᶠ n : Nat in atTop, ∀ T : Finset I,
      (T.biUnion (block n)).card = ∑ i ∈ T, blockSize i) :
    Tendsto (fun n : Nat => sourceIndexedBlocksCoveredWeight
      (calibrationExponent lam hlam n) (block n)) atTop
      (𝓝 (∑ T ∈ (Finset.univ : Finset I).powerset,
        (-1 : ℝ) ^ T.card *
          Real.exp (-(((∑ i ∈ T, blockSize i : Nat) : ℝ) * lam)))) := by
  let P : Finset (Finset I) := (Finset.univ : Finset I).powerset
  have hterm : ∀ T ∈ P, Tendsto (fun n : Nat =>
      (-1 : ℝ) ^ T.card *
        coverageMissProfile
            (cappedZipfDegreeMass
              (calibrationExponent lam hlam n) (sourceReactionCount n))
            (sourceReactionCount n) (T.biUnion (block n)).card ^
          sourceMoleculeCount n) atTop
      (𝓝 ((-1 : ℝ) ^ T.card *
        Real.exp (-(((∑ i ∈ T, blockSize i : Nat) : ℝ) * lam)))) := by
    intro T hT
    let M : Nat := ∑ i ∈ T, blockSize i
    have hfixed : Tendsto (fun n : Nat =>
        coverageMissProfile
            (cappedZipfDegreeMass
              (calibrationExponent lam hlam n) (sourceReactionCount n))
            (sourceReactionCount n) M ^
          sourceMoleculeCount n) atTop
        (𝓝 (Real.exp (-((M : ℝ) * lam)))) := by
      by_cases hM : M = 0
      · have ha : ∀ᶠ n : Nat in atTop,
            1 < calibrationExponent lam hlam n :=
          (calibrationExponent_tendsto_two lam hlam)
            (Ioi_mem_nhds one_lt_two)
        have heq : ∀ᶠ n : Nat in atTop,
            coverageMissProfile
                (cappedZipfDegreeMass
                  (calibrationExponent lam hlam n) (sourceReactionCount n))
                (sourceReactionCount n) 0 ^ sourceMoleculeCount n = 1 := by
          filter_upwards [eventually_ge_atTop 4, ha] with n hn han
          rw [powerLawCoverageMissProfile_zero
            (calibrationExponent lam hlam n) han (sourceReactionCount n) (by
              have hp : 2 ≤ 2 ^ n := by
                simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2)
                  (by omega : 1 ≤ n)
              exact hp.trans (sourceReactionCount_bounds hn).1), one_pow]
        have hone : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1) :=
          tendsto_const_nhds
        have hconv : Tendsto (fun n : Nat =>
            coverageMissProfile
                (cappedZipfDegreeMass
                  (calibrationExponent lam hlam n) (sourceReactionCount n))
                (sourceReactionCount n) 0 ^ sourceMoleculeCount n)
            atTop (𝓝 1) := by
          apply hone.congr'
          filter_upwards [heq] with n hn
          exact hn.symm
        simpa [M, hM] using hconv
      · simpa [M, powerLawSeedClosedProbability,
          powerLawCoverageMissProfile_eq] using
          calibratedPowerLawSeedClosed lam hlam M (Nat.pos_of_ne_zero hM)
    have hmiss : Tendsto (fun n : Nat =>
        coverageMissProfile
            (cappedZipfDegreeMass
              (calibrationExponent lam hlam n) (sourceReactionCount n))
            (sourceReactionCount n) (T.biUnion (block n)).card ^
          sourceMoleculeCount n) atTop
        (𝓝 (Real.exp (-((M : ℝ) * lam)))) := by
      apply hfixed.congr'
      filter_upwards [hcard] with n hn
      rw [hn T]
    simpa only [M] using
      (tendsto_const_nhds.mul hmiss)
  have hsum := tendsto_finsetSum P hterm
  have hformula : ∀ᶠ n : Nat in atTop,
      sourceIndexedBlocksCoveredWeight
          (calibrationExponent lam hlam n) (block n) =
        ∑ T ∈ P, (-1 : ℝ) ^ T.card *
          coverageMissProfile
              (cappedZipfDegreeMass
                (calibrationExponent lam hlam n) (sourceReactionCount n))
              (sourceReactionCount n) (T.biUnion (block n)).card ^
            sourceMoleculeCount n := by
    have ha : ∀ᶠ n : Nat in atTop,
        1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam)
        (Ioi_mem_nhds one_lt_two)
    filter_upwards [eventually_ge_atTop 4, ha] with n hn han
    simpa only [P] using sourceIndexedBlocksCoveredWeight_eq
      (calibrationExponent lam hlam n) han hn (block n)
  apply hsum.congr'
  filter_upwards [hformula] with n hn
  exact hn.symm

/-- The alternating fixed-block Poisson expression factors over the blocks. -/
theorem poissonBlockInclusionExclusion_eq_product
    {I : Type*} [DecidableEq I] (S : Finset I)
    (blockSize : I → Nat) (lam : ℝ) :
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
      Real.exp (-(((∑ i ∈ T, blockSize i : Nat) : ℝ) * lam))) =
      ∏ i ∈ S, (1 - Real.exp (-((blockSize i : ℝ) * lam))) := by
  rw [Finset.prod_sub]
  symm
  apply Finset.sum_congr rfl
  intro T hT
  have hexp :
      Real.exp (-(((∑ i ∈ T, blockSize i : Nat) : ℝ) * lam)) =
        ∏ i ∈ T, Real.exp (-((blockSize i : ℝ) * lam)) := by
    rw [← Real.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    rw [← Finset.sum_neg_distrib]
  rw [hexp]
  simp

/-- Product-form restatement of the fixed indexed-block source limit. -/
theorem calibrated_sourceIndexedBlocksCoveredWeight_tendsto_product
    {I : Type*} [Fintype I] [DecidableEq I]
    (lam : ℝ) (hlam : 0 < lam)
    (block : ∀ n : Nat, I → Finset (Reaction n)) (blockSize : I → Nat)
    (hcard : ∀ᶠ n : Nat in atTop, ∀ T : Finset I,
      (T.biUnion (block n)).card = ∑ i ∈ T, blockSize i) :
    Tendsto (fun n : Nat => sourceIndexedBlocksCoveredWeight
      (calibrationExponent lam hlam n) (block n)) atTop
      (𝓝 (∏ i : I,
        (1 - Real.exp (-((blockSize i : ℝ) * lam))))) := by
  rw [← poissonBlockInclusionExclusion_eq_product
    (Finset.univ : Finset I) blockSize lam]
  exact calibrated_sourceIndexedBlocksCoveredWeight_tendsto
    lam hlam block blockSize hcard

end PowerLawSmallRAF
