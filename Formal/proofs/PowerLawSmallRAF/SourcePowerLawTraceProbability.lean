import proofs.PowerLawSmallRAF.ReversibleSupportEnumeration
import proofs.PowerLawSmallRAF.PowerLawSeedDock
import proofs.PowerLawSmallRAF.BinaryReactionEnumeration
import proofs.PowerLawSmallRAF.CoverageInclusionExclusion

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- Molecule-oriented catalysis fibres for the literal split-position source
catalogue. -/
abbrev SourceMoleculeFibreConfig (n : Nat) :=
  Molecule n → Finset (Reaction n)

noncomputable def sourcePowerLawConfigWeight
    (a : ℝ) (n : Nat) (config : SourceMoleculeFibreConfig n) : ℝ :=
  ∏ x : Molecule n,
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n))
      (config x)

theorem sum_sourcePowerLawConfigWeight_eq_one
    (a : ℝ) (n : Nat) (ha : 1 < a) (hn : 4 ≤ n) :
    (∑ config : SourceMoleculeFibreConfig n,
      sourcePowerLawConfigWeight a n config) = 1 := by
  simp only [sourcePowerLawConfigWeight]
  rw [← Fintype.prod_sum]
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hone : ∑ A : Finset (Reaction n),
      subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A = 1 := by
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  simp_rw [hone]
  simp

theorem sourcePowerLawConfigWeight_nonneg
    (a : ℝ) (n : Nat) (ha : 1 < a)
    (config : SourceMoleculeFibreConfig n) :
    0 ≤ sourcePowerLawConfigWeight a n config := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  apply Finset.prod_nonneg
  intro x hx
  exact subsetDegreeWeight_nonneg _
    (fun d => cappedZipfDegreeMass_nonneg a _ d hzpos) (config x)

/-- Exact one-coordinate mass of a prescribed source channel. -/
theorem source_oneFibre_incidence_mass_eq_gatewayHit
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) (r : Reaction n) :
    (∑ A : Finset (Reaction n),
      if r ∈ A then
        subsetDegreeWeight
          (cappedZipfDegreeMass a (sourceReactionCount n)) A
      else 0) =
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := by
  classical
  let w : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hwsum : ∑ A : Finset (Reaction n), w A = 1 := by
    dsimp [w]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Reaction n))) (fun A => r ∈ A) w
  have hmiss : (∑ A : Finset (Reaction n), if r ∉ A then w A else 0) =
      finitePowerLawMoleculeMiss a {r} := by
    rw [finitePowerLawMoleculeMiss]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hr : r ∈ A
    · simp [hr, w]
    · simp only [w, Finset.disjoint_singleton_right, hr, not_false_eq_true]
      rw [← hcard]
  rw [finitePowerLawMoleculeMiss_eq_gatewayMiss, hcard] at hmiss
  simp only [Finset.card_singleton] at hmiss
  have hhitFilter : (∑ A : Finset (Reaction n), if r ∈ A then w A else 0) =
      ∑ A ∈ (Finset.univ : Finset (Finset (Reaction n))).filter
        (fun A => r ∈ A), w A := by rw [Finset.sum_filter]
  have hmissFilter : (∑ A : Finset (Reaction n), if r ∉ A then w A else 0) =
      ∑ A ∈ (Finset.univ : Finset (Finset (Reaction n))).filter
        (fun A => ¬ r ∈ A), w A := by rw [Finset.sum_filter]
  rw [hwsum] at hsplit
  dsimp [powerLawMoleculeGatewayHit]
  change (∑ A : Finset (Reaction n), if r ∈ A then w A else 0) = _
  linarith [hsplit, hhitFilter, hmissFilter]

/-- The exact product-law marginal of one molecule-channel incidence. -/
theorem source_single_incidence_mass_eq_gatewayHit
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (x : Molecule n) (r : Reaction n) :
    (∑ config : SourceMoleculeFibreConfig n,
      if r ∈ config x then sourcePowerLawConfigWeight a n config else 0) =
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := by
  classical
  let w : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hwsum : ∑ A : Finset (Reaction n), w A = 1 := by
    dsimp [w]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  have hhit : (∑ A : Finset (Reaction n), if r ∈ A then w A else 0) =
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Finset (Reaction n))) (fun A => r ∈ A) w
    have hmiss : (∑ A : Finset (Reaction n), if r ∉ A then w A else 0) =
        finitePowerLawMoleculeMiss a {r} := by
      rw [finitePowerLawMoleculeMiss]
      apply Finset.sum_congr rfl
      intro A hA
      by_cases hr : r ∈ A
      · simp [hr, w]
      · simp only [w, Finset.disjoint_singleton_right, hr,
          not_false_eq_true]
        rw [← hcard]
    rw [finitePowerLawMoleculeMiss_eq_gatewayMiss, hcard] at hmiss
    simp only [Finset.card_singleton] at hmiss
    have hhitFilter : (∑ A : Finset (Reaction n), if r ∈ A then w A else 0) =
        ∑ A ∈ (Finset.univ : Finset (Finset (Reaction n))).filter
          (fun A => r ∈ A), w A := by rw [Finset.sum_filter]
    have hmissFilter : (∑ A : Finset (Reaction n), if r ∉ A then w A else 0) =
        ∑ A ∈ (Finset.univ : Finset (Finset (Reaction n))).filter
          (fun A => ¬ r ∈ A), w A := by rw [Finset.sum_filter]
    rw [hwsum] at hsplit
    dsimp [powerLawMoleculeGatewayHit]
    linarith [hsplit, hhitFilter, hmissFilter]
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if r ∈ config x then ∏ y, w (config y) else 0) =
        ∏ y, if y = x then (if r ∈ config y then w (config y) else 0)
          else w (config y) := by
    intro config
    by_cases hr : r ∈ config x
    · simp only [if_pos hr]
      apply Finset.prod_congr rfl
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp [hr]
      · simp [hyx]
    · simp only [if_neg hr]
      rw [Finset.prod_eq_zero (Finset.mem_univ x)]
      simp [hr]
  change (∑ config : SourceMoleculeFibreConfig n,
    if r ∈ config x then ∏ y, w (config y) else 0) = _
  simp_rw [hpoint]
  rw [← Fintype.prod_sum (fun y (A : Finset (Reaction n)) =>
    if y = x then (if r ∈ A then w A else 0) else w A)]
  have hcoordinate : ∀ y : Molecule n,
      (∑ A : Finset (Reaction n),
        if y = x then (if r ∈ A then w A else 0) else w A) =
        if y = x then powerLawMoleculeGatewayHit a (sourceReactionCount n) 1
        else 1 := by
    intro y
    split_ifs with hy
    · exact hhit
    · exact hwsum
  simp_rw [hcoordinate]
  rw [Finset.prod_ite_eq' Finset.univ x]
  simp

theorem source_single_incidence_mass_le_mean_div
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (x : Molecule n) (r : Reaction n) :
    (∑ config : SourceMoleculeFibreConfig n,
      if r ∈ config x then sourcePowerLawConfigWeight a n config else 0) ≤
      windowZipfMean a (sourceReactionCount n) / sourceReactionCount n := by
  rw [source_single_incidence_mass_eq_gatewayHit a ha hn x r]
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hpred : sourceReactionCount n - 1 + 1 = sourceReactionCount n := by
    omega
  simpa [hpred] using (powerLawMoleculeGatewayHit_bounds a
    (sourceReactionCount n) 1 ha hR (by omega) (by omega)).2

/-- Distinct active catalyst identities contribute independent prescribed-edge
costs, even when two hubs select the same scaffold reaction. -/
theorem source_gatewayMap_mass_eq_pow
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (gateway : ↥H → Reaction n) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ x : ↥H, gateway x ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) =
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ^ H.card := by
  classical
  let w : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hwsum : ∑ A : Finset (Reaction n), w A = 1 := by
    dsimp [w]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  let p := powerLawMoleculeGatewayHit a (sourceReactionCount n) 1
  let f : Molecule n → Finset (Reaction n) → ℝ := fun y A =>
    if hy : y ∈ H then
      (if gateway ⟨y, hy⟩ ∈ A then w A else 0)
    else w A
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if ∀ x : ↥H, gateway x ∈ config x then ∏ y, w (config y) else 0) =
        ∏ y, f y (config y) := by
    intro config
    by_cases hall : ∀ x : ↥H, gateway x ∈ config x
    · simp only [if_pos hall]
      apply Finset.prod_congr rfl
      intro y hyU
      by_cases hy : y ∈ H
      · simp only [f, dif_pos hy, if_pos (hall ⟨y, hy⟩)]
      · simp only [f, dif_neg hy]
    · simp only [if_neg hall]
      push Not at hall
      obtain ⟨x, hx⟩ := hall
      rw [Finset.prod_eq_zero (Finset.mem_univ (x : Molecule n))]
      simp only [f, dif_pos x.property, if_neg hx]
  change (∑ config : SourceMoleculeFibreConfig n,
    if ∀ x : ↥H, gateway x ∈ config x then ∏ y, w (config y) else 0) = _
  simp_rw [hpoint]
  change (∑ config : SourceMoleculeFibreConfig n, ∏ y, f y (config y)) = _
  rw [← Fintype.prod_sum f]
  have hcoordinate : ∀ y : Molecule n,
      (∑ A : Finset (Reaction n), f y A) =
        if y ∈ H then p else 1 := by
    intro y
    by_cases hy : y ∈ H
    · simp only [f, dif_pos hy, if_pos hy, p, w]
      exact source_oneFibre_incidence_mass_eq_gatewayHit
        a ha hn (gateway ⟨y, hy⟩)
    · simp [f, hy, hwsum]
  simp_rw [hcoordinate]
  dsimp [p]
  rw [Finset.prod_ite]
  simp

/-- Exact one-fibre mass of avoiding a fixed source reaction set. -/
theorem source_oneFibre_miss_mass_eq_coverageMiss
    {n : Nat} (a : ℝ) (hn : 4 ≤ n) (targets : Finset (Reaction n)) :
    (∑ A : Finset (Reaction n),
      if Disjoint A targets then
        subsetDegreeWeight
          (cappedZipfDegreeMass a (sourceReactionCount n)) A
      else 0) =
      coverageMissProfile
        (cappedZipfDegreeMass a (sourceReactionCount n))
        (sourceReactionCount n) targets.card := by
  classical
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  rw [← hcard]
  exact (finitePowerLawMoleculeMiss_eq_gatewayMiss a targets).trans
    (powerLawCoverageMissProfile_eq a (Fintype.card (Reaction n))
      targets.card).symm

/-- Distinct molecule fibres avoid the same fixed target set independently. -/
theorem source_jointMiss_mass_eq_pow
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (targets : Finset (Reaction n)) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ x : ↥H, Disjoint (config x) targets then
        sourcePowerLawConfigWeight a n config else 0) =
      coverageMissProfile
          (cappedZipfDegreeMass a (sourceReactionCount n))
          (sourceReactionCount n) targets.card ^ H.card := by
  classical
  let w : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hwsum : ∑ A : Finset (Reaction n), w A = 1 := by
    dsimp [w]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  let u := coverageMissProfile
    (cappedZipfDegreeMass a (sourceReactionCount n))
    (sourceReactionCount n) targets.card
  let f : Molecule n → Finset (Reaction n) → ℝ := fun y A =>
    if y ∈ H then (if Disjoint A targets then w A else 0) else w A
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if ∀ x : ↥H, Disjoint (config x) targets then
          ∏ y, w (config y) else 0) = ∏ y, f y (config y) := by
    intro config
    by_cases hall : ∀ x : ↥H, Disjoint (config x) targets
    · simp only [if_pos hall]
      apply Finset.prod_congr rfl
      intro y hyU
      by_cases hy : y ∈ H
      · simp only [f, if_pos hy, if_pos (hall ⟨y, hy⟩)]
      · simp only [f, if_neg hy]
    · simp only [if_neg hall]
      push Not at hall
      obtain ⟨x, hx⟩ := hall
      rw [Finset.prod_eq_zero (Finset.mem_univ (x : Molecule n))]
      simp only [f, if_pos x.property, if_neg hx]
  change (∑ config : SourceMoleculeFibreConfig n,
    if ∀ x : ↥H, Disjoint (config x) targets then
      ∏ y, w (config y) else 0) = _
  simp_rw [hpoint]
  change (∑ config : SourceMoleculeFibreConfig n, ∏ y, f y (config y)) = _
  rw [← Fintype.prod_sum f]
  have hcoordinate : ∀ y : Molecule n,
      (∑ A : Finset (Reaction n), f y A) = if y ∈ H then u else 1 := by
    intro y
    by_cases hy : y ∈ H
    · simp only [f, if_pos hy, u, w]
      exact source_oneFibre_miss_mass_eq_coverageMiss a hn targets
    · simp [f, hy, hwsum]
  simp_rw [hcoordinate]
  dsimp [u]
  rw [Finset.prod_ite]
  simp

/-- Exact source-model coverage kernel for a fixed reaction support and a
fixed set of candidate catalysts.  This retains all overlap correlations. -/
theorem source_fixedCoverage_mass_eq_powerLawCoverageProbability
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (S : Finset (Reaction n)) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) =
      powerLawCoverageProbability a (sourceReactionCount n) S.card H.card := by
  classical
  let miss : Reaction n → Finset (SourceMoleculeFibreConfig n) := fun r =>
    Finset.univ.filter fun config => ∀ x : ↥H, r ∉ config x
  let weight : SourceMoleculeFibreConfig n → ℝ :=
    sourcePowerLawConfigWeight a n
  let u : Nat → ℝ := fun j =>
    coverageMissProfile
      (cappedZipfDegreeMass a (sourceReactionCount n))
      (sourceReactionCount n) j
  have hintersection : ∀ t ∈ S.powerset,
      (∑ config ∈ t.inf miss, weight config) = u t.card ^ H.card := by
    intro t ht
    have hset : t.inf miss =
        Finset.univ.filter (fun config =>
          ∀ x : ↥H, Disjoint (config x) t) := by
      ext config
      simp only [Finset.mem_inf, Finset.mem_univ, Finset.mem_filter, true_and,
        miss]
      constructor
      · intro h x
        rw [Finset.disjoint_left]
        intro r hrConfig hrT
        exact h r hrT x hrConfig
      · intro h r hrT x hrConfig
        exact (Finset.disjoint_left.mp (h x)) hrConfig hrT
    rw [hset, ← source_jointMiss_mass_eq_pow a ha hn H t]
    symm
    rw [Finset.sum_filter]
  have hIE := allCoveredWeight_eq_coverageInclusionExclusion
    S miss weight u H.card hintersection
  rw [powerLawCoverageProbability]
  change _ = coverageInclusionExclusion u S.card H.card
  rw [← hIE]
  rw [allCoveredWeight]
  have hset : S.inf (fun r => (miss r)ᶜ) =
      Finset.univ.filter (fun config =>
        ∀ r ∈ S, ∃ x ∈ H, r ∈ config x) := by
    ext config
    simp only [Finset.mem_inf, Finset.mem_compl, Finset.mem_filter,
      Finset.mem_univ, true_and, miss]
    constructor
    · intro h r hr
      push Not at h
      obtain ⟨x, hx⟩ := h r hr
      exact ⟨x, x.property, hx⟩
    · intro h r hr
      push Not
      obtain ⟨x, hxH, hxr⟩ := h r hr
      exact ⟨⟨x, hxH⟩, hxr⟩
  rw [hset, Finset.sum_filter]

/-- A prescribed reaction being catalyzed by at least one molecule from a
finite candidate set costs at most the candidate-set cardinality times the
one-incidence marginal.  No independence between candidate molecules is used
in this union bound. -/
theorem source_incidence_union_mass_le
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (r : Reaction n) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
      (H.card : ℝ) *
        (windowZipfMean a (sourceReactionCount n) /
          sourceReactionCount n) := by
  classical
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if ∃ x ∈ H, r ∈ config x then
          sourcePowerLawConfigWeight a n config else 0) ≤
        ∑ x ∈ H, if r ∈ config x then
          sourcePowerLawConfigWeight a n config else 0 := by
    intro config
    by_cases hex : ∃ x ∈ H, r ∈ config x
    · have hevent : ∃ x ∈ H, r ∈ config x := hex
      obtain ⟨x, hxH, hxr⟩ := hex
      simp only [if_pos hevent]
      have hsingle := Finset.single_le_sum
        (s := H) (f := fun y => if r ∈ config y then
          sourcePowerLawConfigWeight a n config else 0)
        (fun y hy => by
          by_cases hry : r ∈ config y
          · simp [hry, sourcePowerLawConfigWeight_nonneg a n ha config]
          · simp [hry]) hxH
      simpa only [if_pos hxr] using hsingle
    · simp only [if_neg hex]
      exact Finset.sum_nonneg fun x hx => by
        by_cases hxr : r ∈ config x
        · simp [hxr, sourcePowerLawConfigWeight_nonneg a n ha config]
        · simp [hxr]
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
        ∑ config : SourceMoleculeFibreConfig n,
          ∑ x ∈ H, if r ∈ config x then
            sourcePowerLawConfigWeight a n config else 0 :=
      Finset.sum_le_sum fun config hconfig => hpoint config
    _ = ∑ x ∈ H, ∑ config : SourceMoleculeFibreConfig n,
          if r ∈ config x then
            sourcePowerLawConfigWeight a n config else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ H, powerLawMoleculeGatewayHit a
          (sourceReactionCount n) 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact source_single_incidence_mass_eq_gatewayHit a ha hn x r
    _ = (H.card : ℝ) * powerLawMoleculeGatewayHit a
          (sourceReactionCount n) 1 := by simp
    _ ≤ (H.card : ℝ) *
        (windowZipfMean a (sourceReactionCount n) /
          sourceReactionCount n) := by
      have hR : 2 ≤ sourceReactionCount n := by
        have hp : 2 ≤ 2 ^ n := by
          simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2)
            (by omega : 1 ≤ n)
        exact hp.trans (sourceReactionCount_bounds hn).1
      have hpred : sourceReactionCount n - 1 + 1 =
          sourceReactionCount n := by omega
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg H.card)
      simpa [hpred] using (powerLawMoleculeGatewayHit_bounds a
        (sourceReactionCount n) 1 ha hR (by omega) (by omega)).2

def sourceCatalysisOfConfig {n : Nat} (config : SourceMoleculeFibreConfig n) :
    Catalysis (Molecule n) (Reaction n) :=
  fun x r => r ∈ config x

noncomputable def sourceFixedRevRAFMass
    (a : ℝ) (n : Nat) (S : Finset (Reaction n)) : ℝ := by
  classical
  exact ∑ config : SourceMoleculeFibreConfig n,
    if IsRevRAF (binaryPolymerCRS n 2)
        (sourceCatalysisOfConfig config) S then
      sourcePowerLawConfigWeight a n config else 0

/-- The full trace supplied by food generation can be chosen independently of
the catalytic configuration while retaining all closure-reachable catalysts. -/
theorem source_revFoodGenerated_has_full_saturated_trace
    {n : Nat} (S : Finset (Reaction n))
    (hfg : RevFoodGenerated (binaryPolymerCRS n 2) S) :
    ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset (binaryFood n 2) S.card ∧
      trace.toFinset = S ∧
      ∀ k, revClosureAt (binaryPolymerCRS n 2) S k ⊆
        reversibleTraceAvailable (binaryFood n 2) trace := by
  obtain ⟨trace, htrace, hsub, hlength, hsaturated⟩ :=
    exists_saturated_reversible_trace (binaryFood n 2) S
  have hSsub : S ⊆ trace.toFinset := by
    intro r hr
    obtain ⟨stage, hendpoints⟩ := hfg r hr
    apply List.mem_toFinset.mpr
    apply hsaturated r hr
    left
    constructor
    · apply revClosureAt_subset_saturated_traceAvailable S trace hsaturated
      apply hendpoints
      simp [binaryPolymerCRS]
    · apply revClosureAt_subset_saturated_traceAvailable S trace hsaturated
      apply hendpoints
      simp [binaryPolymerCRS]
  have heq : trace.toFinset = S := Finset.Subset.antisymm hsub hSsub
  have hnodup := (mem_reversibleTraceFinset_length_nodup htrace).2
  have hlen : trace.length = S.card := by
    rw [← List.toFinset_card_of_nodup hnodup, heq]
  exact ⟨trace, by simpa only [hlen] using htrace, heq,
    fun k => revClosureAt_subset_saturated_traceAvailable S trace hsaturated⟩

/-- Exact-kernel fixed-support RAF bound.  Food generation fixes a trace and
all catalysts available to the RAF lie in its trace-available molecule set;
the full correlated coverage cost is therefore the source coverage kernel. -/
theorem source_fixed_revRAF_mass_le_exact_coverage
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (S : Finset (Reaction n))
    (hfg : RevFoodGenerated (binaryPolymerCRS n 2) S) :
    ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset (binaryFood n 2) S.card ∧
      trace.toFinset = S ∧
      sourceFixedRevRAFMass a n S ≤
        powerLawCoverageProbability a (sourceReactionCount n) S.card
          (reversibleTraceAvailable (binaryFood n 2) trace).card := by
  classical
  obtain ⟨trace, htrace, heq, hclosure⟩ :=
    source_revFoodGenerated_has_full_saturated_trace S hfg
  let H := reversibleTraceAvailable (binaryFood n 2) trace
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if IsRevRAF (binaryPolymerCRS n 2)
          (sourceCatalysisOfConfig config) S then
        sourcePowerLawConfigWeight a n config else 0) ≤
      (if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) := by
    intro config
    by_cases hraf : IsRevRAF (binaryPolymerCRS n 2)
        (sourceCatalysisOfConfig config) S
    · have hcovered : ∀ r, r ∈ S →
          ∃ x : Molecule n, x ∈ H ∧ r ∈ config x := by
        intro r hrS
        obtain ⟨x, k, hx, hcat⟩ := hraf.2.2 r hrS
        exact ⟨x, hclosure k hx, hcat⟩
      rw [if_pos hraf, if_pos hcovered]
    · simp only [if_neg hraf]
      by_cases hcovered : ∀ r, r ∈ S →
          ∃ x : Molecule n, x ∈ H ∧ r ∈ config x
      · rw [if_pos hcovered]
        exact sourcePowerLawConfigWeight_nonneg a n ha config
      · rw [if_neg hcovered]
  refine ⟨trace, htrace, heq, ?_⟩
  rw [sourceFixedRevRAFMass]
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if IsRevRAF (binaryPolymerCRS n 2)
          (sourceCatalysisOfConfig config) S then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ config : SourceMoleculeFibreConfig n,
        if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
          sourcePowerLawConfigWeight a n config else 0 :=
      Finset.sum_le_sum fun config hconfig => hpoint config
    _ = powerLawCoverageProbability a (sourceReactionCount n) S.card H.card :=
      source_fixedCoverage_mass_eq_powerLawCoverageProbability a ha hn H S

/-- A fixed nonempty food-generated support can be an RAF only if one fixed
reaction of that support receives an incidence from the support's trace
availability set.  This is the correlation-robust fixed-support estimate. -/
theorem source_fixed_revRAF_mass_le_trace_union
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (S : Finset (Reaction n)) (hne : S.Nonempty)
    (hfg : RevFoodGenerated (binaryPolymerCRS n 2) S) :
    ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset (binaryFood n 2) S.card ∧
      trace.toFinset = S ∧
      sourceFixedRevRAFMass a n S ≤
        ((reversibleTraceAvailable (binaryFood n 2) trace).card : ℝ) *
          (windowZipfMean a (sourceReactionCount n) /
            sourceReactionCount n) := by
  classical
  obtain ⟨trace, htrace, heq, hclosure⟩ :=
    source_revFoodGenerated_has_full_saturated_trace S hfg
  obtain ⟨r, hrS⟩ := hne
  let H := reversibleTraceAvailable (binaryFood n 2) trace
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if IsRevRAF (binaryPolymerCRS n 2)
          (sourceCatalysisOfConfig config) S then
        sourcePowerLawConfigWeight a n config else 0) ≤
      (if ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) := by
    intro config
    by_cases hraf : IsRevRAF (binaryPolymerCRS n 2)
        (sourceCatalysisOfConfig config) S
    · obtain ⟨x, k, hx, hcat⟩ := hraf.2.2 r hrS
      have hxH : x ∈ H := hclosure k hx
      have hevent : ∃ y ∈ H, r ∈ config y :=
        ⟨x, hxH, hcat⟩
      simp [hraf, hevent]
    · simp only [if_neg hraf]
      by_cases hevent : ∃ x ∈ H, r ∈ config x
      · simp [hevent, sourcePowerLawConfigWeight_nonneg a n ha config]
      · simp [hevent]
  refine ⟨trace, htrace, heq, ?_⟩
  rw [sourceFixedRevRAFMass]
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if IsRevRAF (binaryPolymerCRS n 2)
          (sourceCatalysisOfConfig config) S then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ config : SourceMoleculeFibreConfig n,
        if ∃ x ∈ H, r ∈ config x then
          sourcePowerLawConfigWeight a n config else 0 :=
      Finset.sum_le_sum fun config hconfig => hpoint config
    _ ≤ (H.card : ℝ) *
        (windowZipfMean a (sourceReactionCount n) /
          sourceReactionCount n) :=
      source_incidence_union_mass_le a ha hn H r

end PowerLawSmallRAF
