import proofs.PowerLawSmallRAF.SourceCriticalJointMiss
import proofs.PowerLawSmallRAF.SourceSplitBlockProbability

namespace PowerLawSmallRAF
open Filter Topology RAF RAF.Polymer RAF.Concrete
noncomputable section

/-- Open requirements with simultaneous closed requirements. The definition
retains the exact configuration weight, including all row correlations. -/
def finiteMarkedPatternWeight {I Ω : Type*} [DecidableEq I]
    [Fintype Ω] [DecidableEq Ω] (S C : Finset I)
    (miss : I → Finset Ω) (w : Ω → ℝ) : ℝ :=
  allCoveredWeight S miss (fun ω => if ω ∈ C.inf miss then w ω else 0)

theorem finiteMarkedPatternWeight_eq {I Ω : Type*} [DecidableEq I]
    [Fintype Ω] [DecidableEq Ω] (S C : Finset I)
    (miss : I → Finset Ω) (w : Ω → ℝ) :
    finiteMarkedPatternWeight S C miss w =
      ∑ T ∈ S.powerset, (-1 : ℝ)^T.card *
        ∑ ω ∈ (T ∪ C).inf miss, w ω := by
  rw [finiteMarkedPatternWeight, allCoveredWeight,
    Finset.inclusion_exclusion_sum_inf_compl]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext ω
  simp [Finset.mem_inf, or_imp, forall_and]

theorem sourceIndexedJointMissWeight_eq {I : Type*} [DecidableEq I]
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (block : I → Finset (Reaction n)) (T : Finset I) :
    (∑ config ∈ T.inf (sourceIndexedBlockMissEvent block),
      sourcePowerLawConfigWeight a n config) =
      coverageMissProfile (cappedZipfDegreeMass a (sourceReactionCount n))
        (sourceReactionCount n) (T.biUnion block).card ^ sourceMoleculeCount n := by
  classical
  have heq : T.inf (sourceIndexedBlockMissEvent block) =
      Finset.univ.filter (fun config : SourceMoleculeFibreConfig n =>
        ∀ x : ↥(Finset.univ : Finset (Molecule n)),
          Disjoint (config x) (T.biUnion block)) := by
    ext config
    simp only [Finset.mem_inf, sourceIndexedBlockMissEvent, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.disjoint_left, Finset.mem_biUnion]
    constructor
    · intro h x r hr ⟨i, hi, hri⟩
      exact h i hi x hr hri
    · intro h i hi x r hr hri
      exact h ⟨x, Finset.mem_univ x⟩ hr ⟨i, hi, hri⟩
  rw [heq, Finset.sum_filter, source_jointMiss_mass_eq_pow a ha hn]
  rw [Finset.card_univ, card_binaryMolecule_eq_sourceMoleculeCount]

theorem sourceExactCriticalMissProfile_tendsto (M : Nat) :
    Tendsto (fun n : Nat => coverageMissProfile
      (cappedZipfDegreeMass (2-2/(n : ℝ)) (sourceReactionCount n))
      (sourceReactionCount n) M ^ sourceMoleculeCount n) atTop
      (𝓝 (Real.exp (-((M : ℝ)*criticalLambda (-2))))) := by
  by_cases hM : M = 0
  · subst M
    simp only [Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [sourceExactCriticalExponent_tendsto.eventually
      (Ioi_mem_nhds one_lt_two)] with n hn
    rw [powerLawCoverageMissProfile_zero _ hn _ (by simp [sourceReactionCount]), one_pow]
  · simpa [powerLawSeedClosedProbability, powerLawCoverageMissProfile_eq] using
      sourceExactCriticalPowerLawSeedClosed M (Nat.pos_of_ne_zero hM)

/-- Any fixed marked/unmarked pattern has its exact finite inclusion-exclusion
limit. The blocks may move with n, provided their union cardinalities stabilize.
Singleton injective coordinates specialize this to a finite channel pattern. -/
theorem sourceExactCriticalPattern_tendsto {I : Type*} [DecidableEq I]
    (S C : Finset I) (block : ∀ n : Nat, I → Finset (Reaction n))
    (size : Finset I → Nat)
    (hcard : ∀ᶠ n : Nat in atTop, ∀ T ∈ S.powerset,
      ((T ∪ C).biUnion (block n)).card = size (T ∪ C)) :
    Tendsto (fun n : Nat => finiteMarkedPatternWeight S C
      (sourceIndexedBlockMissEvent (block n))
      (sourcePowerLawConfigWeight (2-2/(n : ℝ)) n)) atTop
      (𝓝 (∑ T ∈ S.powerset, (-1 : ℝ)^T.card *
        Real.exp (-((size (T ∪ C) : ℝ)*criticalLambda (-2))))) := by
  classical
  have hterm : ∀ T ∈ S.powerset, Tendsto (fun n : Nat =>
      (-1 : ℝ)^T.card * coverageMissProfile
        (cappedZipfDegreeMass (2-2/(n : ℝ)) (sourceReactionCount n))
        (sourceReactionCount n) ((T ∪ C).biUnion (block n)).card ^
        sourceMoleculeCount n) atTop
      (𝓝 ((-1 : ℝ)^T.card *
        Real.exp (-((size (T ∪ C) : ℝ)*criticalLambda (-2))))) := by
    intro T hT
    have hh := (sourceExactCriticalMissProfile_tendsto (size (T ∪ C))).const_mul
      ((-1 : ℝ)^T.card)
    apply hh.congr'
    filter_upwards [hcard] with n hn
    rw [hn T hT]
  have hsum := tendsto_finsetSum S.powerset hterm
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 4, sourceExactCriticalExponent_tendsto.eventually
    (Ioi_mem_nhds one_lt_two)] with n hn han
  rw [finiteMarkedPatternWeight_eq]
  apply Finset.sum_congr rfl
  intro T hT
  rw [sourceIndexedJointMissWeight_eq _ han hn]

theorem disjointPatternLimit_eq (I : Type*) [DecidableEq I]
    (S C : Finset I) (hSC : Disjoint S C) (lam : ℝ) :
    (∑ T ∈ S.powerset, (-1 : ℝ)^T.card *
      Real.exp (-(((T ∪ C).card : ℝ)*lam))) =
      (1-Real.exp (-lam))^S.card * Real.exp (-((C.card : ℝ)*lam)) := by
  have hsum : (∑ T ∈ S.powerset, (-1 : ℝ)^T.card *
      Real.exp (-((T.card : ℝ)*lam))) = (1-Real.exp (-lam))^S.card := by
    simpa using poissonBlockInclusionExclusion_eq_product S (fun _ => 1) lam
  rw [← hsum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T hT
  have hTC : Disjoint T C := hSC.mono_left (Finset.mem_powerset.mp hT)
  rw [Finset.card_union_of_disjoint hTC, Nat.cast_add]
  rw [show -(((T.card : ℝ)+(C.card : ℝ))*lam) =
    -((T.card : ℝ)*lam) + -((C.card : ℝ)*lam) by ring, Real.exp_add]
  ring

/-- Explicit iid pattern limit for finitely many distinct channel coordinates.
Only eventual finite union cardinalities are assumed; the source remains the
literal capped-Zipf configuration law. -/
theorem sourceExactCriticalDistinctPattern_tendsto {I : Type*} [DecidableEq I]
    (S C : Finset I) (hSC : Disjoint S C)
    (block : ∀ n : Nat, I → Finset (Reaction n))
    (hcard : ∀ᶠ n : Nat in atTop, ∀ T ∈ S.powerset,
      ((T ∪ C).biUnion (block n)).card = (T ∪ C).card) :
    Tendsto (fun n : Nat => finiteMarkedPatternWeight S C
      (sourceIndexedBlockMissEvent (block n))
      (sourcePowerLawConfigWeight (2-2/(n : ℝ)) n)) atTop
      (𝓝 ((1-Real.exp (-criticalLambda (-2)))^S.card *
        Real.exp (-((C.card : ℝ)*criticalLambda (-2))))) := by
  rw [← disjointPatternLimit_eq I S C hSC (criticalLambda (-2))]
  exact sourceExactCriticalPattern_tendsto S C block Finset.card hcard

end
end PowerLawSmallRAF
