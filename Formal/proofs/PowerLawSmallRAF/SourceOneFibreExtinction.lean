import proofs.PowerLawSmallRAF.SourceSelfGeneratingFibreRAF
import proofs.PowerLawSmallRAF.FiniteProductVariance
import proofs.PowerLawSmallRAF.SourceBandGlobalCoverage
import proofs.HordijkSteelThreshold.ExponentialWitnessSize

namespace PowerLawSmallRAF

noncomputable section

open RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold
open Filter Topology
open scoped BigOperators

/-- Every possible owner molecule reachable from one fibre lies in this
literal food-plus-reaction-support envelope. -/
def sourceFibreOwnerEnvelope {n : Nat} (A : Finset (Reaction n)) :
    Finset (Molecule n) :=
  binaryFood n 2 ∪ revReactionSupport (binaryPolymerCRS n 2) A

theorem source_selfGeneratingFibre_owner_mem_envelope {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    (hself : SourceSelfGeneratingFibre config x) :
    x ∈ sourceFibreOwnerEnvelope (config x) := by
  obtain ⟨k, hx⟩ := hself.2.2
  exact revClosureAt_subset_food_union_support
    (binaryPolymerCRS n 2) (config x) k hx

theorem card_sourceFibreOwnerEnvelope_le_support {n : Nat}
    (A : Finset (Reaction n)) :
    (sourceFibreOwnerEnvelope A).card ≤ 6 + 3 * A.card := by
  rw [sourceFibreOwnerEnvelope]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (card_binaryFood_two_le_six n)
      (card_revReactionSupport_binary_le A))

theorem card_sourceFibreOwnerEnvelope_le_catalogue {n : Nat}
    (A : Finset (Reaction n)) :
    (sourceFibreOwnerEnvelope A).card ≤ sourceMoleculeCount n := by
  calc
    (sourceFibreOwnerEnvelope A).card ≤
        (Finset.univ : Finset (Molecule n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = sourceMoleculeCount n := by
      rw [Finset.card_univ, card_binaryMolecule_eq_sourceMoleculeCount]

noncomputable def sourceExistsSelfGeneratingFibreWeight
    (a : ℝ) (n : Nat) : ℝ := by
  classical
  exact ∑ config : SourceMoleculeFibreConfig n,
    if ∃ x : Molecule n, SourceSelfGeneratingFibre config x then
      sourcePowerLawConfigWeight a n config else 0

/-- Union bound after retaining only the two necessary one-fibre conditions:
the owner is reachable from its fibre and that fibre hits a seed channel. -/
theorem sourceExistsSelfGeneratingFibreWeight_le_ownerSeedSum
    (a : ℝ) (ha : 1 < a) (n : Nat) :
    sourceExistsSelfGeneratingFibreWeight a n ≤
      ∑ x : Molecule n,
        ∑ config : SourceMoleculeFibreConfig n,
          if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
              x ∈ sourceFibreOwnerEnvelope (config x) then
            sourcePowerLawConfigWeight a n config else 0 := by
  classical
  rw [sourceExistsSelfGeneratingFibreWeight]
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if ∃ x : Molecule n, SourceSelfGeneratingFibre config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ config : SourceMoleculeFibreConfig n,
        ∑ x : Molecule n,
          if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
              x ∈ sourceFibreOwnerEnvelope (config x) then
            sourcePowerLawConfigWeight a n config else 0 := by
      apply Finset.sum_le_sum
      intro config hconfig
      by_cases hex : ∃ x : Molecule n, SourceSelfGeneratingFibre config x
      · rw [if_pos hex]
        obtain ⟨x, hx⟩ := hex
        have hseed := source_selfGeneratingFibre_has_internal_seed hx
        have howner := source_selfGeneratingFibre_owner_mem_envelope hx
        have hs := Finset.single_le_sum
          (s := (Finset.univ : Finset (Molecule n)))
          (f := fun z : Molecule n =>
            if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config z) ∧
                z ∈ sourceFibreOwnerEnvelope (config z) then
              sourcePowerLawConfigWeight a n config else 0)
          (fun z hz => by
            dsimp
            split_ifs
            · exact sourcePowerLawConfigWeight_nonneg a n ha config
            · exact le_rfl)
          (Finset.mem_univ x)
        calc
          sourcePowerLawConfigWeight a n config =
              (if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
                  x ∈ sourceFibreOwnerEnvelope (config x) then
                sourcePowerLawConfigWeight a n config else 0) := by
            rw [if_pos ⟨hseed, howner⟩]
          _ ≤ ∑ z : Molecule n,
              if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config z) ∧
                  z ∈ sourceFibreOwnerEnvelope (config z) then
                sourcePowerLawConfigWeight a n config else 0 := hs
      · rw [if_neg hex]
        apply Finset.sum_nonneg
        intro x hx
        split_ifs
        · exact sourcePowerLawConfigWeight_nonneg a n ha config
        · exact le_rfl
    _ = ∑ x : Molecule n,
        ∑ config : SourceMoleculeFibreConfig n,
          if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
              x ∈ sourceFibreOwnerEnvelope (config x) then
            sourcePowerLawConfigWeight a n config else 0 :=
      Finset.sum_comm

/-- The correct one-owner event allows a food-generated scaffold strictly
inside the sampled fibre; unused reactions of that fibre need not themselves
be food-generated. -/
def SourceOneFibreScaffold {n : Nat}
    (config : SourceMoleculeFibreConfig n) (x : Molecule n) : Prop :=
  ∃ S : Finset (Reaction n),
    S ⊆ config x ∧ S.Nonempty ∧
      RevFoodGenerated (binaryPolymerCRS n 2) S ∧
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k

noncomputable def sourceExistsOneFibreScaffoldWeight
    (a : ℝ) (n : Nat) : ℝ := by
  classical
  exact ∑ config : SourceMoleculeFibreConfig n,
    if ∃ x : Molecule n, SourceOneFibreScaffold config x then
      sourcePowerLawConfigWeight a n config else 0

theorem source_oneFibreScaffold_owner_seed {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    (h : SourceOneFibreScaffold config x) :
    (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
      x ∈ sourceFibreOwnerEnvelope (config x) := by
  obtain ⟨S, hsub, hne, hfood, k, hx⟩ := h
  have hseed := source_fibreScaffold_has_internal_seed hsub hne hfood
  have hx' := revClosureAt_mono_reactions (binaryPolymerCRS n 2) hsub k hx
  exact ⟨hseed, revClosureAt_subset_food_union_support
    (binaryPolymerCRS n 2) (config x) k hx'⟩

theorem sourceExistsOneFibreScaffoldWeight_le_ownerSeedSum
    (a : ℝ) (ha : 1 < a) (n : Nat) :
    sourceExistsOneFibreScaffoldWeight a n ≤
      ∑ x : Molecule n,
        ∑ config : SourceMoleculeFibreConfig n,
          if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
              x ∈ sourceFibreOwnerEnvelope (config x) then
            sourcePowerLawConfigWeight a n config else 0 := by
  classical
  rw [sourceExistsOneFibreScaffoldWeight]
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if ∃ x : Molecule n, SourceOneFibreScaffold config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ config : SourceMoleculeFibreConfig n,
        ∑ x : Molecule n,
          if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
              x ∈ sourceFibreOwnerEnvelope (config x) then
            sourcePowerLawConfigWeight a n config else 0 := by
      apply Finset.sum_le_sum
      intro config hconfig
      by_cases hex : ∃ x : Molecule n, SourceOneFibreScaffold config x
      · rw [if_pos hex]
        obtain ⟨x, hx⟩ := hex
        have hnecessary := source_oneFibreScaffold_owner_seed hx
        have hs := Finset.single_le_sum
          (s := (Finset.univ : Finset (Molecule n)))
          (f := fun z : Molecule n =>
            if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config z) ∧
                z ∈ sourceFibreOwnerEnvelope (config z) then
              sourcePowerLawConfigWeight a n config else 0)
          (fun z hz => by
            dsimp
            split_ifs
            · exact sourcePowerLawConfigWeight_nonneg a n ha config
            · exact le_rfl)
          (Finset.mem_univ x)
        calc
          sourcePowerLawConfigWeight a n config =
              (if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
                  x ∈ sourceFibreOwnerEnvelope (config x) then
                sourcePowerLawConfigWeight a n config else 0) := by
            rw [if_pos hnecessary]
          _ ≤ ∑ z : Molecule n,
              if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config z) ∧
                  z ∈ sourceFibreOwnerEnvelope (config z) then
                sourcePowerLawConfigWeight a n config else 0 := hs
      · rw [if_neg hex]
        apply Finset.sum_nonneg
        intro x hx
        split_ifs
        · exact sourcePowerLawConfigWeight_nonneg a n ha config
        · exact le_rfl
    _ = ∑ x : Molecule n,
        ∑ config : SourceMoleculeFibreConfig n,
          if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
              x ∈ sourceFibreOwnerEnvelope (config x) then
            sourcePowerLawConfigWeight a n config else 0 := Finset.sum_comm

noncomputable def sourceOneFibreOwnerSeedProfile
    (a : ℝ) (n : Nat) : ℝ :=
  ∑ A : Finset (Reaction n),
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A *
      (if ∃ r ∈ sourceSeedReactionFinset n, r ∈ A then
        (sourceFibreOwnerEnvelope A).card else 0)

theorem source_ownerSeed_coordinate_mass_eq
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (x : Molecule n) :
    (∑ config : SourceMoleculeFibreConfig n,
      if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
          x ∈ sourceFibreOwnerEnvelope (config x) then
        sourcePowerLawConfigWeight a n config else 0) =
      ∑ A : Finset (Reaction n),
        subsetDegreeWeight
            (cappedZipfDegreeMass a (sourceReactionCount n)) A *
          (if (∃ r ∈ sourceSeedReactionFinset n, r ∈ A) ∧
              x ∈ sourceFibreOwnerEnvelope A then 1 else 0) := by
  classical
  let p : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  let g : Finset (Reaction n) → ℝ := fun A =>
    if (∃ r ∈ sourceSeedReactionFinset n, r ∈ A) ∧
        x ∈ sourceFibreOwnerEnvelope A then 1 else 0
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hp : ∑ A, p A = 1 := by
    dsimp [p]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  have hmarg := finiteProduct_expectation_coordinate
    (I := Molecule n) p g hp x
  simpa only [p, g, sourcePowerLawConfigWeight, mul_ite, mul_one,
    mul_zero] using hmarg

theorem source_ownerSeedSum_eq_profile
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) :
    (∑ x : Molecule n,
      ∑ config : SourceMoleculeFibreConfig n,
        if (∃ r ∈ sourceSeedReactionFinset n, r ∈ config x) ∧
            x ∈ sourceFibreOwnerEnvelope (config x) then
          sourcePowerLawConfigWeight a n config else 0) =
      sourceOneFibreOwnerSeedProfile a n := by
  classical
  simp_rw [source_ownerSeed_coordinate_mass_eq a ha hn]
  rw [sourceOneFibreOwnerSeedProfile, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Finset.mul_sum]
  by_cases hseed : ∃ r ∈ sourceSeedReactionFinset n, r ∈ A
  · rw [if_pos hseed]
    congr 1
    calc
      (∑ x : Molecule n,
          if (∃ r ∈ sourceSeedReactionFinset n, r ∈ A) ∧
              x ∈ sourceFibreOwnerEnvelope A then 1 else 0) =
          ∑ x ∈ sourceFibreOwnerEnvelope A, (1 : ℝ) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext x
          simp [hseed]
        · intro x hx
          rfl
      _ = (sourceFibreOwnerEnvelope A).card := by simp
  · rw [if_neg hseed]
    simp [hseed]

theorem sourceExistsSelfGeneratingFibreWeight_le_profile
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) :
    sourceExistsSelfGeneratingFibreWeight a n ≤
      sourceOneFibreOwnerSeedProfile a n := by
  exact (sourceExistsSelfGeneratingFibreWeight_le_ownerSeedSum a ha n).trans_eq
    (source_ownerSeedSum_eq_profile a ha hn)

theorem sourceExistsOneFibreScaffoldWeight_le_profile
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) :
    sourceExistsOneFibreScaffoldWeight a n ≤
      sourceOneFibreOwnerSeedProfile a n := by
  exact (sourceExistsOneFibreScaffoldWeight_le_ownerSeedSum a ha n).trans_eq
    (source_ownerSeedSum_eq_profile a ha hn)

/-- Target-hit mass with an arbitrary nonnegative weight depending on the
sampled fibre cardinality. -/
noncomputable def sourceCardWeightedTargetHit
    (a : ℝ) (n : Nat) (f : Nat → ℝ)
    (targets : Finset (Reaction n)) : ℝ :=
  ∑ A : Finset (Reaction n),
    if ¬ Disjoint A targets then
      subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A *
        f A.card
    else 0

theorem sourceCardWeightedTargetHit_eq_degreeSum
    (a : ℝ) {n : Nat} (hn : 2 ≤ n) (f : Nat → ℝ)
    (targets : Finset (Reaction n)) :
    sourceCardWeightedTargetHit a n f targets =
      ∑ d ∈ Finset.range (sourceReactionCount n),
        cappedZipfDegreeMass a (sourceReactionCount n) d * f d *
          (1 - hypergeometricGatewayMiss
            (sourceReactionCount n) targets.card d) := by
  classical
  let q : Nat → ℝ := fun d =>
    cappedZipfDegreeMass a (sourceReactionCount n) d * f d
  let w : Finset (Reaction n) → ℝ := fun A => subsetDegreeWeight q A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) hn
  have hfull : q (Fintype.card (Reaction n)) = 0 := by
    simp [q, hcard, cappedZipfDegreeMass]
  have hmiss :
      (∑ A : Finset (Reaction n), if Disjoint A targets then w A else 0) =
        coverageMissProfile q (Fintype.card (Reaction n)) targets.card :=
    finiteDegreeMassMoleculeMiss_eq_coverageMiss q targets hfull
  rw [hcard] at hmiss
  have htotal0 := sum_subsetDegreeWeight_eq_mass_sum
    (J := Reaction n) q
  rw [hcard, Finset.sum_range_succ, show q (sourceReactionCount n) = 0 by
    simpa [hcard] using hfull, add_zero] at htotal0
  have hsplit :
      (∑ A : Finset (Reaction n), if Disjoint A targets then w A else 0) +
        (∑ A : Finset (Reaction n), if ¬ Disjoint A targets then w A else 0) =
          ∑ A : Finset (Reaction n), w A := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hdis : Disjoint A targets <;> simp [hdis]
  have hhit : sourceCardWeightedTargetHit a n f targets =
      ∑ A : Finset (Reaction n), if ¬ Disjoint A targets then w A else 0 := by
    rw [sourceCardWeightedTargetHit]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hdis : Disjoint A targets
    · simp [hdis]
    · simp only [if_pos hdis]
      dsimp [w, q, subsetDegreeWeight]
      ring
  rw [hhit]
  calc
    (∑ A : Finset (Reaction n), if ¬ Disjoint A targets then w A else 0) =
        (∑ d ∈ Finset.range (sourceReactionCount n), q d) -
          coverageMissProfile q (sourceReactionCount n) targets.card := by
      have htotal : (∑ A : Finset (Reaction n), w A) =
          ∑ d ∈ Finset.range (sourceReactionCount n), q d := by
        simpa [w] using htotal0
      linarith
    _ = ∑ d ∈ Finset.range (sourceReactionCount n),
        cappedZipfDegreeMass a (sourceReactionCount n) d * f d *
          (1 - hypergeometricGatewayMiss
            (sourceReactionCount n) targets.card d) := by
      rw [coverageMissProfile]
      simp_rw [degreeMissProbability_eq_gatewayMiss]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [q]
      ring

theorem sourceCardWeightedTargetHit_le_degreeMoment
    (a : ℝ) (ha : 1 < a) {n : Nat} (hn : 4 ≤ n)
    (f : Nat → ℝ) (hf : ∀ d, 0 ≤ f d)
    (targets : Finset (Reaction n)) (hM0 : 0 < targets.card)
    (hMR : targets.card ≤ sourceReactionCount n) :
    sourceCardWeightedTargetHit a n f targets ≤
      ((targets.card : ℝ) /
        ((sourceReactionCount n - targets.card + 1 : Nat) : ℝ)) *
        ∑ d ∈ Finset.range (sourceReactionCount n),
          cappedZipfDegreeMass a (sourceReactionCount n) d * f d * d := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  rw [sourceCardWeightedTargetHit_eq_degreeSum a (by omega), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdR : d < sourceReactionCount n := Finset.mem_range.mp hd
  have hmass : 0 ≤ cappedZipfDegreeMass a (sourceReactionCount n) d :=
    cappedZipfDegreeMass_nonneg a (sourceReactionCount n) d hzpos
  have hhit := (hypergeometricGatewayHit_envelope
    (sourceReactionCount n) targets.card d hM0 hMR hdR).2
  calc
    cappedZipfDegreeMass a (sourceReactionCount n) d * f d *
        (1 - hypergeometricGatewayMiss
          (sourceReactionCount n) targets.card d) ≤
      cappedZipfDegreeMass a (sourceReactionCount n) d * f d *
        ((targets.card : ℝ) * (d : ℝ) /
          ((sourceReactionCount n - targets.card + 1 : Nat) : ℝ)) :=
      mul_le_mul_of_nonneg_left hhit (mul_nonneg hmass (hf d))
    _ = (targets.card : ℝ) /
        ((sourceReactionCount n - targets.card + 1 : Nat) : ℝ) *
          (cappedZipfDegreeMass a (sourceReactionCount n) d * f d * d) := by
      ring

theorem sourceSeedReactionFinset_nonempty {n : Nat} (hn : 2 ≤ n) :
    (sourceSeedReactionFinset n).Nonempty := by
  let k : Fin n := ⟨1, by omega⟩
  let w : Word (k.val + 1) := ⟨0, by simp [k]⟩
  let s : Fin k.val := ⟨0, by simp [k]⟩
  let r : Reaction n := ⟨k, (w, s)⟩
  refine ⟨r, ?_⟩
  simp [sourceSeedReactionFinset, RevSeedReaction, binaryPolymerCRS,
    binaryFood, r, k, w, s, reactionProductLength]

theorem sourceOneFibreOwnerSeedProfile_le_weightedHit
    (a : ℝ) (ha : 1 < a) {n : Nat} :
    sourceOneFibreOwnerSeedProfile a n ≤
      sourceCardWeightedTargetHit a n
        (fun d => ((min (sourceMoleculeCount n) (6 + 3 * d) : Nat) : ℝ))
        (sourceSeedReactionFinset n) := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  rw [sourceOneFibreOwnerSeedProfile, sourceCardWeightedTargetHit]
  apply Finset.sum_le_sum
  intro A hA
  have hseedIff : (∃ r ∈ sourceSeedReactionFinset n, r ∈ A) ↔
      ¬ Disjoint A (sourceSeedReactionFinset n) := by
    rw [Finset.not_disjoint_iff]
    constructor
    · rintro ⟨r, hrseed, hrA⟩
      exact ⟨r, hrA, hrseed⟩
    · rintro ⟨r, hrA, hrseed⟩
      exact ⟨r, hrseed, hrA⟩
  have henv : (sourceFibreOwnerEnvelope A).card ≤
      min (sourceMoleculeCount n) (6 + 3 * A.card) := by
    exact le_min (card_sourceFibreOwnerEnvelope_le_catalogue A)
      (card_sourceFibreOwnerEnvelope_le_support A)
  have hmass : 0 ≤ subsetDegreeWeight
      (cappedZipfDegreeMass a (sourceReactionCount n)) A :=
    subsetDegreeWeight_nonneg _
      (fun d => cappedZipfDegreeMass_nonneg a _ d hzpos) A
  by_cases hseed : ∃ r ∈ sourceSeedReactionFinset n, r ∈ A
  · rw [if_pos hseed, if_pos (hseedIff.mp hseed)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast henv) hmass
  · rw [if_neg hseed, if_neg (mt hseedIff.mpr hseed)]
    norm_num

theorem sourceReactionCount_ge_68 {n : Nat} (hn : 4 ≤ n) :
    68 ≤ sourceReactionCount n := by
  rw [sourceReactionCount]
  have hp : 32 ≤ 2 ^ (n + 1) := by
    simpa only [show 32 = 2 ^ 5 by norm_num] using
      Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 5 ≤ n + 1)
  have hc : 2 ≤ n - 2 := by omega
  nlinarith [Nat.mul_le_mul hc hp]

/-- Exact degree-moment envelope for all one-fibre self-generating events. -/
theorem sourceExistsSelfGeneratingFibreWeight_le_degreeMoment
    (a : ℝ) (ha : 1 < a) {n : Nat} (hn : 4 ≤ n) :
    sourceExistsSelfGeneratingFibreWeight a n ≤
      (((sourceSeedReactionFinset n).card : ℝ) /
        ((sourceReactionCount n - (sourceSeedReactionFinset n).card + 1 : Nat) : ℝ)) *
        ∑ d ∈ Finset.range (sourceReactionCount n),
          cappedZipfDegreeMass a (sourceReactionCount n) d *
            (min (sourceMoleculeCount n) (6 + 3 * d) : Nat) * d := by
  calc
    sourceExistsSelfGeneratingFibreWeight a n ≤
        sourceOneFibreOwnerSeedProfile a n :=
      sourceExistsSelfGeneratingFibreWeight_le_profile a ha hn
    _ ≤ sourceCardWeightedTargetHit a n
        (fun d => ((min (sourceMoleculeCount n) (6 + 3 * d) : Nat) : ℝ))
        (sourceSeedReactionFinset n) :=
      sourceOneFibreOwnerSeedProfile_le_weightedHit a ha
    _ ≤ (((sourceSeedReactionFinset n).card : ℝ) /
        ((sourceReactionCount n - (sourceSeedReactionFinset n).card + 1 : Nat) : ℝ)) *
        ∑ d ∈ Finset.range (sourceReactionCount n),
          cappedZipfDegreeMass a (sourceReactionCount n) d *
            (min (sourceMoleculeCount n) (6 + 3 * d) : Nat) * d := by
      apply sourceCardWeightedTargetHit_le_degreeMoment a ha hn
      · intro d
        positivity
      · exact (sourceSeedReactionFinset_nonempty (by omega)).card_pos
      · exact (card_sourceSeedReactionFinset_le_68 n).trans
          (sourceReactionCount_ge_68 hn)

theorem sourceExistsOneFibreScaffoldWeight_le_degreeMoment
    (a : ℝ) (ha : 1 < a) {n : Nat} (hn : 4 ≤ n) :
    sourceExistsOneFibreScaffoldWeight a n ≤
      (((sourceSeedReactionFinset n).card : ℝ) /
        ((sourceReactionCount n - (sourceSeedReactionFinset n).card + 1 : Nat) : ℝ)) *
        ∑ d ∈ Finset.range (sourceReactionCount n),
          cappedZipfDegreeMass a (sourceReactionCount n) d *
            (min (sourceMoleculeCount n) (6 + 3 * d) : Nat) * d := by
  calc
    sourceExistsOneFibreScaffoldWeight a n ≤
        sourceOneFibreOwnerSeedProfile a n :=
      sourceExistsOneFibreScaffoldWeight_le_profile a ha hn
    _ ≤ sourceCardWeightedTargetHit a n
        (fun d => ((min (sourceMoleculeCount n) (6 + 3 * d) : Nat) : ℝ))
        (sourceSeedReactionFinset n) :=
      sourceOneFibreOwnerSeedProfile_le_weightedHit a ha
    _ ≤ (((sourceSeedReactionFinset n).card : ℝ) /
        ((sourceReactionCount n - (sourceSeedReactionFinset n).card + 1 : Nat) : ℝ)) *
        ∑ d ∈ Finset.range (sourceReactionCount n),
          cappedZipfDegreeMass a (sourceReactionCount n) d *
            (min (sourceMoleculeCount n) (6 + 3 * d) : Nat) * d := by
      apply sourceCardWeightedTargetHit_le_degreeMoment a ha hn
      · intro d
        positivity
      · exact (sourceSeedReactionFinset_nonempty (by omega)).card_pos
      · exact (card_sourceSeedReactionFinset_le_68 n).trans
          (sourceReactionCount_ge_68 hn)

/-- The Zipf normalizer contains its unit atom. -/
theorem one_le_zipfNormalizer (a : ℝ) (ha : 1 < a) :
    1 ≤ zipfNormalizer a := by
  rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
  have hpow : 0 ≤ (2 : ℝ) ^ (-a) := Real.rpow_nonneg (by positivity) _
  have htail : 0 ≤ rpowTail a 2 := rpowTail_nonneg a 2
  linarith

/-- Before a cutoff, every non-cap degree contributes at most one critical
window factor to the unnormalized second moment. -/
theorem cappedZipfDegreeMass_mul_sq_le_windowFactor
    (a C : ℝ) (n R d : Nat) (hC : 0 ≤ C) (ha1 : 1 < a)
    (ha : 2 - C / (n : ℝ) ≤ a) (hd : d + 1 < R) :
    cappedZipfDegreeMass a R d * (d : ℝ) ^ 2 ≤
      (R : ℝ) ^ (C / (n : ℝ)) := by
  by_cases hd0 : d = 0
  · subst d
    simp
    positivity
  · have hk : d + 1 ∈ Finset.Ico 2 R := by
      simp only [Finset.mem_Ico]
      omega
    have hraw := interiorSecondTerm_le_windowFactor a C n R (d + 1) hC ha hk
    have hz : 1 ≤ zipfNormalizer a := one_le_zipfNormalizer a ha1
    have hzpos : 0 < zipfNormalizer a := lt_of_lt_of_le zero_lt_one hz
    rw [cappedZipfDegreeMass, if_pos hd]
    have heq : (((d + 1 - 1 : Nat) : ℝ) ^ 2 *
        ((d : ℝ) + 1) ^ (-a)) /
          zipfNormalizer a =
        (((d : ℝ) + 1) ^ (-a) /
          zipfNormalizer a) * (d : ℝ) ^ 2 := by
      rw [show d + 1 - 1 = d by omega]
      ring
    rw [Nat.cast_add, Nat.cast_one] at hraw
    rw [← heq]
    exact (div_le_self (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by positivity) _)) hz).trans hraw

theorem oneFibreDegreeMomentTerm_le_cutoff
    (a C : ℝ) (n X R L d : Nat) (hC : 0 ≤ C)
    (ha32 : (3 / 2 : ℝ) ≤ a) (ha : 2 - C / (n : ℝ) ≤ a)
    (hL0 : 0 < L) (hLR : L < R) (hdR : d < R) :
    cappedZipfDegreeMass a R d * (min X (6 + 3 * d) : Nat) * d ≤
      9 * (R : ℝ) ^ (C / (n : ℝ)) * (if d < L then 1 else 0) +
        ((X : ℝ) / (L : ℝ)) *
          (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) := by
  have ha1 : 1 < a := by linarith
  have hzpos : 0 < zipfNormalizer a :=
    lt_of_lt_of_le zero_lt_one (one_le_zipfNormalizer a ha1)
  have hmass : 0 ≤ cappedZipfDegreeMass a R d :=
    cappedZipfDegreeMass_nonneg a R d hzpos
  by_cases hdL : d < L
  · rw [if_pos hdL]
    have hdcap : d + 1 < R := by omega
    have hsquare := cappedZipfDegreeMass_mul_sq_le_windowFactor
      a C n R d hC ha1 ha hdcap
    by_cases hd0 : d = 0
    · subst d
      simp
      positivity
    · have henv : min X (6 + 3 * d) ≤ 9 * d := by
        exact (Nat.min_le_right _ _).trans (by omega)
      have hmain : cappedZipfDegreeMass a R d *
          (min X (6 + 3 * d) : Nat) * d ≤
          9 * (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) := by
        have henvR : ((min X (6 + 3 * d) : Nat) : ℝ) ≤ 9 * (d : ℝ) := by
          exact_mod_cast henv
        calc
          cappedZipfDegreeMass a R d * (min X (6 + 3 * d) : Nat) * d ≤
              cappedZipfDegreeMass a R d * (9 * (d : ℝ)) * d := by
            gcongr
          _ = 9 * (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) := by ring
      have hfirst : 9 * (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) ≤
          9 * (R : ℝ) ^ (C / (n : ℝ)) := by gcongr
      have htail : 0 ≤ ((X : ℝ) / (L : ℝ)) *
          (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) := by positivity
      exact hmain.trans (by
        simpa only [mul_one] using hfirst.trans (le_add_of_nonneg_right htail))
  · rw [if_neg hdL, mul_zero, zero_add]
    have hLd : L ≤ d := le_of_not_gt hdL
    have henv : min X (6 + 3 * d) ≤ X := Nat.min_le_left _ _
    have hLdR : (L : ℝ) ≤ (d : ℝ) := by exact_mod_cast hLd
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
    have hscale : ((X : ℝ) * (d : ℝ)) ≤
        ((X : ℝ) / (L : ℝ)) * (d : ℝ) ^ 2 := by
      rw [show ((X : ℝ) / (L : ℝ)) * (d : ℝ) ^ 2 =
        ((X : ℝ) * (d : ℝ) ^ 2) / (L : ℝ) by ring]
      apply (le_div_iff₀ hLpos).2
      have hmul := mul_le_mul_of_nonneg_left hLdR
        (mul_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg d))
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      cappedZipfDegreeMass a R d * (min X (6 + 3 * d) : Nat) * d ≤
          cappedZipfDegreeMass a R d * X * d := by gcongr
      _ ≤ cappedZipfDegreeMass a R d *
          (((X : ℝ) / (L : ℝ)) * (d : ℝ) ^ 2) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hmass
      _ = ((X : ℝ) / (L : ℝ)) *
          (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) := by ring

/-- A cutoff below the cap turns the owner-envelope degree moment into two
explicit terms: a bounded low-degree count and a second-moment tail. -/
theorem oneFibreDegreeMoment_le_cutoffEnvelope
    (a C : ℝ) (n X R L : Nat) (hC : 0 ≤ C)
    (ha32 : (3 / 2 : ℝ) ≤ a) (ha : 2 - C / (n : ℝ) ≤ a)
    (hL0 : 0 < L) (hLR : L < R) (hR : 2 ≤ R) :
    (∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d *
        (min X (6 + 3 * d) : Nat) * d) ≤
      9 * (L : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) +
        ((X : ℝ) / (L : ℝ)) *
          (4 * (R : ℝ) * (R : ℝ) ^ (C / (n : ℝ))) := by
  let F : ℝ := (R : ℝ) ^ (C / (n : ℝ))
  have hpoint : ∀ d ∈ Finset.range R,
      cappedZipfDegreeMass a R d * (min X (6 + 3 * d) : Nat) * d ≤
        9 * F * (if d < L then 1 else 0) +
          ((X : ℝ) / (L : ℝ)) *
            (cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) := by
    intro d hd
    exact oneFibreDegreeMomentTerm_le_cutoff a C n X R L d hC ha32 ha
      hL0 hLR (Finset.mem_range.mp hd)
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hindicator : (∑ d ∈ Finset.range R, (if d < L then (1 : ℝ) else 0)) = L := by
    have hfilter : (Finset.range R).filter (fun d => d < L) = Finset.range L := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter]
    rw [hfilter]
    simp
  rw [hindicator] at hsum
  have ha1 : 1 < a := by linarith
  have hz : 1 ≤ zipfNormalizer a := one_le_zipfNormalizer a ha1
  have hnum0 : 0 ≤ windowZipfSecondNumerator a R :=
    windowZipfSecondNumerator_nonneg a R
  have hsecond : (∑ d ∈ Finset.range R,
      cappedZipfDegreeMass a R d * (d : ℝ) ^ 2) ≤
        4 * (R : ℝ) * F := by
    rw [cappedZipfDegreeSecondMoment_eq a R hR]
    exact (div_le_self hnum0 hz).trans
      (windowZipfSecondNumerator_le_four_mul a C n R hC ha32 ha hR)
  have hcoef : 0 ≤ (X : ℝ) / (L : ℝ) := by positivity
  have htailbound := mul_le_mul_of_nonneg_left hsecond hcoef
  calc
    (∑ d ∈ Finset.range R, cappedZipfDegreeMass a R d *
        (min X (6 + 3 * d) : Nat) * d) ≤
        9 * F * (L : ℝ) + ((X : ℝ) / (L : ℝ)) *
          ∑ d ∈ Finset.range R,
            cappedZipfDegreeMass a R d * (d : ℝ) ^ 2 := hsum
    _ ≤ 9 * F * (L : ℝ) + ((X : ℝ) / (L : ℝ)) *
          (4 * (R : ℝ) * F) := add_le_add (le_refl _) htailbound
    _ = 9 * (L : ℝ) * (R : ℝ) ^ (C / (n : ℝ)) +
        ((X : ℝ) / (L : ℝ)) *
          (4 * (R : ℝ) * (R : ℝ) ^ (C / (n : ℝ))) := by
      dsimp [F]
      ring

theorem source_sqrt_cutoff_pos_lt_reactionCount {n : Nat} (hn : 6 ≤ n) :
    0 < sourceMoleculeCount n * Nat.sqrt n ∧
      sourceMoleculeCount n * Nat.sqrt n < sourceReactionCount n := by
  have hspos : 0 < Nat.sqrt n := Nat.sqrt_pos.2 (by omega)
  have hxpos : 0 < sourceMoleculeCount n :=
    (pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds (by omega)).1
  constructor
  · positivity
  · have hm : 3 ≤ n - 2 := by omega
    have hnlt : n < 2 * (n - 2) := by omega
    have hmul : 2 * (n - 2) ≤ (n - 2) * (n - 2) := by
      exact Nat.mul_le_mul_right (n - 2) (by omega : 2 ≤ n - 2)
    have hs : Nat.sqrt n < n - 2 := Nat.sqrt_lt.2 (hnlt.trans_le hmul)
    have hxpow : sourceMoleculeCount n < 2 ^ (n + 1) := by
      rw [sourceMoleculeCount]
      have hp : 2 ≤ 2 ^ (n + 1) := by
        exact (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n + 1))
      omega
    have hcut : sourceMoleculeCount n * Nat.sqrt n <
        2 ^ (n + 1) * (n - 2) :=
      mul_lt_mul hxpow hs.le hspos (Nat.zero_le _)
    rw [sourceReactionCount]
    nlinarith

theorem sourceSeedFraction_le_68 {n : Nat} (hn : 4 ≤ n) :
    ((sourceSeedReactionFinset n).card : ℝ) /
        ((sourceReactionCount n - (sourceSeedReactionFinset n).card + 1 : Nat) : ℝ) ≤
      68 / ((sourceReactionCount n - 67 : Nat) : ℝ) := by
  let s := (sourceSeedReactionFinset n).card
  let R := sourceReactionCount n
  have hs : s ≤ 68 := card_sourceSeedReactionFinset_le_68 n
  have hR : 68 ≤ R := sourceReactionCount_ge_68 hn
  have hden1 : (0 : ℝ) < (R - s + 1 : Nat) := by positivity
  have hden2 : (0 : ℝ) < (R - 67 : Nat) := by
    exact_mod_cast (by omega : 0 < R - 67)
  have hfirst : (s : ℝ) / (R - s + 1 : Nat) ≤
      68 / (R - s + 1 : Nat) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hs) hden1.le
  have hdens : R - 67 ≤ R - s + 1 := by omega
  have hsecond : (68 : ℝ) / (R - s + 1 : Nat) ≤
      68 / (R - 67 : Nat) := by
    exact div_le_div_of_nonneg_left (by norm_num) hden2
      (by exact_mod_cast hdens)
  exact hfirst.trans hsecond

/-- Fully explicit finite bound for one-fibre RAFs at the square-root cutoff. -/
theorem sourceExistsSelfGeneratingFibreWeight_le_sqrtEnvelope
    (a C : ℝ) {n : Nat} (hn : 6 ≤ n) (hC : 0 ≤ C)
    (ha32 : (3 / 2 : ℝ) ≤ a) (ha : 2 - C / (n : ℝ) ≤ a) :
    sourceExistsSelfGeneratingFibreWeight a n ≤
      (68 / ((sourceReactionCount n - 67 : Nat) : ℝ)) *
        (9 * ((sourceMoleculeCount n * Nat.sqrt n : Nat) : ℝ) *
            (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) +
          ((sourceMoleculeCount n : ℝ) /
              ((sourceMoleculeCount n * Nat.sqrt n : Nat) : ℝ)) *
            (4 * (sourceReactionCount n : ℝ) *
              (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)))) := by
  have ha1 : 1 < a := by linarith
  have hbase := sourceExistsSelfGeneratingFibreWeight_le_degreeMoment a ha1
    (by omega : 4 ≤ n)
  have hcut := source_sqrt_cutoff_pos_lt_reactionCount hn
  have hmoment := oneFibreDegreeMoment_le_cutoffEnvelope a C n
    (sourceMoleculeCount n) (sourceReactionCount n)
    (sourceMoleculeCount n * Nat.sqrt n) hC ha32 ha hcut.1 hcut.2
    (by exact (sourceReactionCount_ge_68 (by omega)).trans' (by norm_num))
  have hmoment0 : 0 ≤ ∑ d ∈ Finset.range (sourceReactionCount n),
      cappedZipfDegreeMass a (sourceReactionCount n) d *
        (min (sourceMoleculeCount n) (6 + 3 * d) : Nat) * d := by
    apply Finset.sum_nonneg
    intro d hd
    have hzpos : 0 < zipfNormalizer a :=
      lt_of_lt_of_le zero_lt_one (one_le_zipfNormalizer a ha1)
    positivity [cappedZipfDegreeMass_nonneg a (sourceReactionCount n) d hzpos]
  have hfrac := sourceSeedFraction_le_68 (n := n) (by omega)
  exact hbase.trans ((mul_le_mul hfrac hmoment hmoment0 (by positivity)).trans_eq rfl)

theorem sourceExistsOneFibreScaffoldWeight_le_sqrtEnvelope
    (a C : ℝ) {n : Nat} (hn : 6 ≤ n) (hC : 0 ≤ C)
    (ha32 : (3 / 2 : ℝ) ≤ a) (ha : 2 - C / (n : ℝ) ≤ a) :
    sourceExistsOneFibreScaffoldWeight a n ≤
      (68 / ((sourceReactionCount n - 67 : Nat) : ℝ)) *
        (9 * ((sourceMoleculeCount n * Nat.sqrt n : Nat) : ℝ) *
            (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) +
          ((sourceMoleculeCount n : ℝ) /
              ((sourceMoleculeCount n * Nat.sqrt n : Nat) : ℝ)) *
            (4 * (sourceReactionCount n : ℝ) *
              (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)))) := by
  have ha1 : 1 < a := by linarith
  have hbase := sourceExistsOneFibreScaffoldWeight_le_degreeMoment a ha1
    (by omega : 4 ≤ n)
  have hcut := source_sqrt_cutoff_pos_lt_reactionCount hn
  have hmoment := oneFibreDegreeMoment_le_cutoffEnvelope a C n
    (sourceMoleculeCount n) (sourceReactionCount n)
    (sourceMoleculeCount n * Nat.sqrt n) hC ha32 ha hcut.1 hcut.2
    (by exact (sourceReactionCount_ge_68 (by omega)).trans' (by norm_num))
  have hmoment0 : 0 ≤ ∑ d ∈ Finset.range (sourceReactionCount n),
      cappedZipfDegreeMass a (sourceReactionCount n) d *
        (min (sourceMoleculeCount n) (6 + 3 * d) : Nat) * d := by
    apply Finset.sum_nonneg
    intro d hd
    have hzpos : 0 < zipfNormalizer a :=
      lt_of_lt_of_le zero_lt_one (one_le_zipfNormalizer a ha1)
    positivity [cappedZipfDegreeMass_nonneg a (sourceReactionCount n) d hzpos]
  have hfrac := sourceSeedFraction_le_68 (n := n) (by omega)
  exact hbase.trans ((mul_le_mul hfrac hmoment hmoment0 (by positivity)).trans_eq rfl)

noncomputable def sourceOneFibreSqrtEnvelope (C : ℝ) (n : Nat) : ℝ :=
  (68 / ((sourceReactionCount n - 67 : Nat) : ℝ)) *
    (9 * ((sourceMoleculeCount n * Nat.sqrt n : Nat) : ℝ) *
        (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) +
      ((sourceMoleculeCount n : ℝ) /
          ((sourceMoleculeCount n * Nat.sqrt n : Nat) : ℝ)) *
        (4 * (sourceReactionCount n : ℝ) *
          (sourceReactionCount n : ℝ) ^ (C / (n : ℝ))))

theorem natSqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  exact ⟨B * B, fun n hn => Nat.le_sqrt.2 hn⟩

theorem natSqrt_cast_inv_tendsto_zero :
    Tendsto (fun n : Nat => ((Nat.sqrt n : Nat) : ℝ)⁻¹) atTop (nhds 0) := by
  exact ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
    natSqrt_tendsto_atTop).inv_tendsto_atTop

theorem natSqrt_div_nat_tendsto_zero :
    Tendsto (fun n : Nat => (Nat.sqrt n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (nhds 0))
    natSqrt_cast_inv_tendsto_zero
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hspos : (0 : ℝ) < Nat.sqrt n := by
      exact_mod_cast (Nat.sqrt_pos.2 hn)
    have hnR : ((Nat.sqrt n : Nat) : ℝ) ^ 2 ≤ (n : ℝ) := by
      exact_mod_cast Nat.sqrt_le' n
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n), inv_eq_one_div,
      one_div]
    calc
      (Nat.sqrt n : ℝ) ≤ (n : ℝ) / (Nat.sqrt n : ℝ) :=
        (le_div_iff₀ hspos).2 (by simpa [pow_two] using hnR)
      _ = (Nat.sqrt n : ℝ)⁻¹ * (n : ℝ) := by ring

theorem sourceOneFibreSqrtEnvelope_tendsto_zero (C : ℝ) :
    Tendsto (sourceOneFibreSqrtEnvelope C) atTop (nhds 0) := by
  have hcat := sourceReactionCount_div_gatewayDenominator_tendsto_one 68 (by norm_num)
  have hnx := sourceReactionCount_div_nat_molecule_tendsto_one.inv₀ one_ne_zero
  have hF : Tendsto (fun n : Nat =>
      (sourceReactionCount n : ℝ) ^ (C / (n : ℝ))) atTop
      (nhds ((2 : ℝ) ^ C)) := by
    simpa only [neg_neg] using sourceReactionCount_rpow_window (-C)
  have hlow := (((tendsto_const_nhds : Tendsto (fun _ : Nat => (612 : ℝ))
      atTop (nhds 612)).mul hcat).mul hnx).mul natSqrt_div_nat_tendsto_zero |>.mul hF
  have hlow0 : Tendsto (fun n : Nat =>
      (612 : ℝ) *
        ((sourceReactionCount n : ℝ) /
          (sourceReactionCount n - 68 + 1 : Nat)) *
        (((sourceReactionCount n : ℝ) /
          ((n : ℝ) * sourceMoleculeCount n))⁻¹) *
        ((Nat.sqrt n : ℝ) / n) *
        (sourceReactionCount n : ℝ) ^ (C / (n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using hlow
  have hhigh := (((tendsto_const_nhds : Tendsto (fun _ : Nat => (272 : ℝ))
      atTop (nhds 272)).mul hcat).mul natSqrt_cast_inv_tendsto_zero).mul hF
  have hhigh0 : Tendsto (fun n : Nat =>
      (272 : ℝ) *
        ((sourceReactionCount n : ℝ) /
          (sourceReactionCount n - 68 + 1 : Nat)) *
        ((Nat.sqrt n : ℝ)⁻¹) *
        (sourceReactionCount n : ℝ) ^ (C / (n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using hhigh
  have hsum := hlow0.add hhigh0
  have hsum0 : Tendsto (fun n : Nat =>
      (612 : ℝ) *
          ((sourceReactionCount n : ℝ) /
            (sourceReactionCount n - 68 + 1 : Nat)) *
          (((sourceReactionCount n : ℝ) /
            ((n : ℝ) * sourceMoleculeCount n))⁻¹) *
          ((Nat.sqrt n : ℝ) / n) *
          (sourceReactionCount n : ℝ) ^ (C / (n : ℝ)) +
        (272 : ℝ) *
          ((sourceReactionCount n : ℝ) /
            (sourceReactionCount n - 68 + 1 : Nat)) *
          ((Nat.sqrt n : ℝ)⁻¹) *
          (sourceReactionCount n : ℝ) ^ (C / (n : ℝ))) atTop (nhds 0) := by
    simpa only [add_zero] using hsum
  apply hsum0.congr'
  filter_upwards [eventually_ge_atTop 6] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hs0 : ((Nat.sqrt n : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sqrt_pos.2 (by omega : 0 < n)))
  have hx0 : (sourceMoleculeCount n : ℝ) ≠ 0 := by
    have hxpos : 0 < sourceMoleculeCount n :=
      (pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds (by omega)).1
    exact_mod_cast (Nat.ne_of_gt hxpos)
  have hRge : 68 ≤ sourceReactionCount n := sourceReactionCount_ge_68 (by omega)
  have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 68)
      (sourceReactionCount_ge_68 (by omega))))
  have hD0 : ((sourceReactionCount n - 67 : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < sourceReactionCount n - 67))
  have hDeq : sourceReactionCount n - 68 + 1 = sourceReactionCount n - 67 := by
    omega
  rw [hDeq]
  rw [sourceOneFibreSqrtEnvelope, Nat.cast_mul]
  field_simp [hn0, hs0, hx0, hR0, hD0]
  ring

/-- One molecule alone cannot support a RAF in the calibrated source model:
the total configuration weight of every self-generating fibre tends to zero. -/
theorem calibrated_sourceExistsSelfGeneratingFibreWeight_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat => sourceExistsSelfGeneratingFibreWeight
      (calibrationExponent lam hlam n) n) atTop (nhds 0) := by
  let b₀ := criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))
  let C : ℝ := |b₀| + 1
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hbound : Tendsto (sourceOneFibreSqrtEnvelope C) atTop (nhds 0) :=
    sourceOneFibreSqrtEnvelope_tendsto_zero C
  have ha32 : ∀ᶠ n : Nat in atTop,
      (3 / 2 : ℝ) ≤ calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam)
      (Ici_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2))
  have hbLower : ∀ᶠ n : Nat in atTop, -C ≤ calibrationB lam hlam n := by
    have hb : -C < b₀ := by
      calc
        -C < -|b₀| := by dsimp [C]; linarith
        _ ≤ b₀ := neg_abs_le b₀
    exact (calibrationB_tendsto_inverse lam hlam)
      (Ici_mem_nhds hb)
  have hevent : ∀ᶠ n : Nat in atTop,
      sourceExistsSelfGeneratingFibreWeight (calibrationExponent lam hlam n) n ≤
        sourceOneFibreSqrtEnvelope C n := by
    filter_upwards [eventually_ge_atTop 6, ha32, hbLower] with n hn ha hB
    have hnpos : (0 : ℝ) < n := by positivity
    have haLower : 2 - C / (n : ℝ) ≤ calibrationExponent lam hlam n := by
      rw [calibrationExponent]
      have hd := div_le_div_of_nonneg_right hB hnpos.le
      calc
        2 - C / (n : ℝ) = 2 + (-C) / (n : ℝ) := by ring
        _ ≤ 2 + calibrationB lam hlam n / (n : ℝ) := by
          simpa only [add_comm] using add_le_add_left hd 2
    exact sourceExistsSelfGeneratingFibreWeight_le_sqrtEnvelope
      (calibrationExponent lam hlam n) C hn hC0 ha haLower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (nhds 0)) hbound
  · have ha1 : ∀ᶠ n : Nat in atTop,
        1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
    filter_upwards [ha1] with n hn
    rw [sourceExistsSelfGeneratingFibreWeight]
    apply Finset.sum_nonneg
    intro config hconfig
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ hn config
    · exact le_rfl
  · exact hevent

/-- Strong one-owner extinction: even when the valid RAF is only a subset of
its owner's sampled fibre, its total calibrated probability tends to zero. -/
theorem calibrated_sourceExistsOneFibreScaffoldWeight_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : Nat => sourceExistsOneFibreScaffoldWeight
      (calibrationExponent lam hlam n) n) atTop (nhds 0) := by
  let b₀ := criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))
  let C : ℝ := |b₀| + 1
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hbound : Tendsto (sourceOneFibreSqrtEnvelope C) atTop (nhds 0) :=
    sourceOneFibreSqrtEnvelope_tendsto_zero C
  have ha32 : ∀ᶠ n : Nat in atTop,
      (3 / 2 : ℝ) ≤ calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam)
      (Ici_mem_nhds (by norm_num : (3 / 2 : ℝ) < 2))
  have hbLower : ∀ᶠ n : Nat in atTop, -C ≤ calibrationB lam hlam n := by
    have hb : -C < b₀ := by
      calc
        -C < -|b₀| := by dsimp [C]; linarith
        _ ≤ b₀ := neg_abs_le b₀
    exact (calibrationB_tendsto_inverse lam hlam) (Ici_mem_nhds hb)
  have hevent : ∀ᶠ n : Nat in atTop,
      sourceExistsOneFibreScaffoldWeight (calibrationExponent lam hlam n) n ≤
        sourceOneFibreSqrtEnvelope C n := by
    filter_upwards [eventually_ge_atTop 6, ha32, hbLower] with n hn ha hB
    have hnpos : (0 : ℝ) < n := by positivity
    have haLower : 2 - C / (n : ℝ) ≤ calibrationExponent lam hlam n := by
      rw [calibrationExponent]
      have hd := div_le_div_of_nonneg_right hB hnpos.le
      calc
        2 - C / (n : ℝ) = 2 + (-C) / (n : ℝ) := by ring
        _ ≤ 2 + calibrationB lam hlam n / (n : ℝ) := by
          simpa only [add_comm] using add_le_add_left hd 2
    exact sourceExistsOneFibreScaffoldWeight_le_sqrtEnvelope
      (calibrationExponent lam hlam n) C hn hC0 ha haLower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (nhds 0)) hbound
  · have ha1 : ∀ᶠ n : Nat in atTop,
        1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
    filter_upwards [ha1] with n hn
    rw [sourceExistsOneFibreScaffoldWeight]
    apply Finset.sum_nonneg
    intro config hconfig
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ hn config
    · exact le_rfl
  · exact hevent

end

end PowerLawSmallRAF
