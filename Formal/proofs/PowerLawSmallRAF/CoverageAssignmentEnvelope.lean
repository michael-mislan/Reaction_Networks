import proofs.PowerLawSmallRAF.SourcePowerLawTraceProbability

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- The reactions assigned to one candidate catalyst. -/
def sourceAssignedBlock {n : Nat}
    (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) (x : ↥H) : Finset (Reaction n) :=
  (S.attach.filter fun r => assignment r = x).image fun r => r.1

/-- Exact mixed mass that one source fibre contains a fixed block. -/
noncomputable def sourceOneFibreContainmentMass {n : Nat}
    (a : ℝ) (T : Finset (Reaction n)) : ℝ :=
  ∑ A : Finset (Reaction n),
    if T ⊆ A then
      subsetDegreeWeight
        (cappedZipfDegreeMass a (sourceReactionCount n)) A
    else 0

theorem sourceOneFibreContainmentMass_nonneg
    {n : Nat} (a : ℝ) (ha : 1 < a) (T : Finset (Reaction n)) :
    0 ≤ sourceOneFibreContainmentMass a T := by
  rw [sourceOneFibreContainmentMass]
  apply Finset.sum_nonneg
  intro A hA
  split_ifs
  · exact subsetDegreeWeight_nonneg _
      (fun d => cappedZipfDegreeMass_nonneg a _ d (by
        rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
        nlinarith [rpowTail_nonneg a 2])) A
  · positivity

theorem sourceOneFibreContainmentMass_empty
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) :
    sourceOneFibreContainmentMass (n := n) a ∅ = 1 := by
  rw [sourceOneFibreContainmentMass]
  simp only [Finset.empty_subset, ↓reduceIte]
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  rw [← hcard]
  exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)

/-- Any nonempty containment block pays at least the exact one-incidence
gateway charge, regardless of how correlated its remaining reactions are. -/
theorem sourceOneFibreContainmentMass_le_gatewayHit_of_mem
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (T : Finset (Reaction n)) (r : Reaction n) (hr : r ∈ T) :
    sourceOneFibreContainmentMass a T ≤
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 := by
  rw [← source_oneFibre_incidence_mass_eq_gatewayHit a ha hn r,
    sourceOneFibreContainmentMass]
  apply Finset.sum_le_sum
  intro A hA
  by_cases hTA : T ⊆ A
  · have hrA := hTA hr
    simp [hTA, hrA]
  · rw [if_neg hTA]
    by_cases hrA : r ∈ A
    · rw [if_pos hrA]
      exact subsetDegreeWeight_nonneg _
        (fun d => cappedZipfDegreeMass_nonneg a _ d (by
          rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
          nlinarith [rpowTail_nonneg a 2])) A
    · rw [if_neg hrA]

/-- Molecule identities actually hit by an assignment. -/
def sourceAssignmentRange {n : Nat}
    (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) : Finset (Molecule n) :=
  Finset.univ.image fun r : ↥S => (assignment r).1

theorem sourceAssignmentRange_subset {n : Nat}
    (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) :
    sourceAssignmentRange S H assignment ⊆ H := by
  intro x hx
  rw [sourceAssignmentRange, Finset.mem_image] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  exact (assignment r).2

theorem sourceAssignedBlock_nonempty_iff_mem_range {n : Nat}
    (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) (x : ↥H) :
    (sourceAssignedBlock S H assignment x).Nonempty ↔
      x.1 ∈ sourceAssignmentRange S H assignment := by
  constructor
  · rintro ⟨r, hr⟩
    rw [sourceAssignedBlock, Finset.mem_image] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    rw [sourceAssignmentRange, Finset.mem_image]
    exact ⟨r', Finset.mem_univ _, congrArg Subtype.val
      (Finset.mem_filter.mp hr').2⟩
  · intro hx
    rw [sourceAssignmentRange, Finset.mem_image] at hx
    obtain ⟨r, hr, hval⟩ := hx
    refine ⟨r.1, ?_⟩
    rw [sourceAssignedBlock, Finset.mem_image]
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply Subtype.ext
    exact hval

/-- Mass of one fixed assignment, retaining all reactions assigned to the
same molecule as a single correlated containment block. -/
noncomputable def sourceAssignmentMass {n : Nat}
    (a : ℝ) (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if ∀ r : ↥S, r.1 ∈ config (assignment r).1 then
      sourcePowerLawConfigWeight a n config
    else 0

/-- Product of the exact block masses, represented on the ambient molecule
type so proof-irrelevant subtype witnesses do not enter later rewrites. -/
noncomputable def sourceAssignmentBlockProduct {n : Nat}
    (a : ℝ) (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) : ℝ :=
  ∏ y : Molecule n, if hy : y ∈ H then
    sourceOneFibreContainmentMass a
      (sourceAssignedBlock S H assignment ⟨y, hy⟩)
  else 1

/-- Independent molecule fibres make the mass of a fixed assignment the
product of its exact same-fibre block masses. -/
theorem sourceAssignmentMass_eq_prod_blocks
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) :
    sourceAssignmentMass a S H assignment =
      sourceAssignmentBlockProduct a S H assignment := by
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
  let f : Molecule n → Finset (Reaction n) → ℝ := fun y A =>
    if hy : y ∈ H then
      if sourceAssignedBlock S H assignment ⟨y, hy⟩ ⊆ A then w A else 0
    else w A
  have hblocks : ∀ config : SourceMoleculeFibreConfig n,
      (∀ r : ↥S, r.1 ∈ config (assignment r).1) ↔
        ∀ x : ↥H, sourceAssignedBlock S H assignment x ⊆ config x.1 := by
    intro config
    constructor
    · intro hall x r hr
      rw [sourceAssignedBlock, Finset.mem_image] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      have hassign := (Finset.mem_filter.mp hr').2
      simpa [hassign] using hall r'
    · intro hall r
      apply hall (assignment r)
      rw [sourceAssignedBlock, Finset.mem_image]
      exact ⟨r, by simp, rfl⟩
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if ∀ r : ↥S, r.1 ∈ config (assignment r).1 then
          ∏ y, w (config y) else 0) = ∏ y, f y (config y) := by
    intro config
    by_cases hall : ∀ r : ↥S, r.1 ∈ config (assignment r).1
    · rw [if_pos hall]
      apply Finset.prod_congr rfl
      intro y hyU
      by_cases hy : y ∈ H
      · simp only [f, dif_pos hy]
        rw [if_pos ((hblocks config).mp hall ⟨y, hy⟩)]
      · simp only [f, dif_neg hy]
    · rw [if_neg hall]
      have hnot := not_congr (hblocks config) |>.mp hall
      push Not at hnot
      obtain ⟨x, hx⟩ := hnot
      rw [Finset.prod_eq_zero (Finset.mem_univ (x : Molecule n))]
      simp only [f, dif_pos x.property, if_neg hx]
  rw [sourceAssignmentMass]
  change (∑ config : SourceMoleculeFibreConfig n,
    if ∀ r : ↥S, r.1 ∈ config (assignment r).1 then
      ∏ y, w (config y) else 0) = _
  simp_rw [hpoint]
  rw [← Fintype.prod_sum f]
  have hcoordinate : ∀ y : Molecule n,
      (∑ A : Finset (Reaction n), f y A) =
        if hy : y ∈ H then
          sourceOneFibreContainmentMass a
            (sourceAssignedBlock S H assignment ⟨y, hy⟩)
        else 1 := by
    intro y
    by_cases hy : y ∈ H
    · simp only [f, dif_pos hy]
      rfl
    · simp [f, hy, hwsum]
  simp_rw [hcoordinate]
  rfl

/-- Each active assignment fibre contributes one gateway factor.  This is the
non-alternating rare-hub charge exposed by the assignment quotient. -/
theorem sourceAssignmentBlockProduct_le_gatewayHit_pow_range
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) :
    sourceAssignmentBlockProduct a S H assignment ≤
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ^
        (sourceAssignmentRange S H assignment).card := by
  classical
  let p := powerLawMoleculeGatewayHit a (sourceReactionCount n) 1
  let range := sourceAssignmentRange S H assignment
  have hpoint : ∀ y : Molecule n,
      (if hy : y ∈ H then
        sourceOneFibreContainmentMass a
          (sourceAssignedBlock S H assignment ⟨y, hy⟩)
      else 1) ≤ if y ∈ range then p else 1 := by
    intro y
    by_cases hyr : y ∈ range
    · have hyH := sourceAssignmentRange_subset S H assignment hyr
      rw [if_pos hyr, dif_pos hyH]
      obtain ⟨r, hr⟩ :=
        (sourceAssignedBlock_nonempty_iff_mem_range S H assignment
          ⟨y, hyH⟩).mpr hyr
      exact sourceOneFibreContainmentMass_le_gatewayHit_of_mem
        a ha hn _ r hr
    · rw [if_neg hyr]
      by_cases hyH : y ∈ H
      · rw [dif_pos hyH]
        have hempty : sourceAssignedBlock S H assignment ⟨y, hyH⟩ = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp
            (fun hne => hyr ((sourceAssignedBlock_nonempty_iff_mem_range
              S H assignment ⟨y, hyH⟩).mp hne))
        rw [hempty, sourceOneFibreContainmentMass_empty a ha hn]
      · rw [dif_neg hyH]
  have hnonneg : ∀ y ∈ (Finset.univ : Finset (Molecule n)),
      0 ≤ if hy : y ∈ H then
        sourceOneFibreContainmentMass a
          (sourceAssignedBlock S H assignment ⟨y, hy⟩)
      else 1 := by
    intro y hy
    by_cases hyH : y ∈ H
    · rw [dif_pos hyH]
      exact sourceOneFibreContainmentMass_nonneg a ha _
    · rw [dif_neg hyH]
      norm_num
  rw [sourceAssignmentBlockProduct]
  calc
    (∏ y : Molecule n, if hy : y ∈ H then
      sourceOneFibreContainmentMass a
        (sourceAssignedBlock S H assignment ⟨y, hy⟩) else 1) ≤
        ∏ y : Molecule n, if y ∈ range then p else 1 :=
      Finset.prod_le_prod hnonneg (fun y hy => hpoint y)
    _ = p ^ range.card := by
      rw [Finset.prod_ite]
      simp [range]

/-- Positive assignment-partition envelope for exact fixed-set coverage. -/
theorem source_fixedCoverage_mass_le_assignment_sum
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (S : Finset (Reaction n)) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ assignment : ↥S → ↥H,
        sourceAssignmentBlockProduct a S H assignment := by
  classical
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
          sourcePowerLawConfigWeight a n config else 0) ≤
        ∑ assignment : ↥S → ↥H,
          if ∀ r : ↥S, r.1 ∈ config (assignment r).1 then
            sourcePowerLawConfigWeight a n config else 0 := by
    intro config
    by_cases hcover : ∀ r ∈ S, ∃ x ∈ H, r ∈ config x
    · let assignment : ↥S → ↥H := fun r =>
        ⟨Classical.choose (hcover r.1 r.2),
          (Classical.choose_spec (hcover r.1 r.2)).1⟩
      have hassignment : ∀ r : ↥S,
          r.1 ∈ config (assignment r).1 := fun r =>
        (Classical.choose_spec (hcover r.1 r.2)).2
      rw [if_pos hcover]
      have hnonneg : ∀ f : ↥S → ↥H, f ∈ Finset.univ →
          0 ≤ (if ∀ r : ↥S, r.1 ∈ config (f r).1 then
            sourcePowerLawConfigWeight a n config else 0) := by
        intro f hf
        by_cases hall : ∀ r : ↥S, r.1 ∈ config (f r).1
        · rw [if_pos hall]
          exact sourcePowerLawConfigWeight_nonneg a n ha config
        · rw [if_neg hall]
      have hsingle := Finset.single_le_sum hnonneg
        (Finset.mem_univ assignment)
      rw [if_pos hassignment] at hsingle
      exact hsingle
    · rw [if_neg hcover]
      exact Finset.sum_nonneg fun assignment hmem => by
        split_ifs
        · exact sourcePowerLawConfigWeight_nonneg a n ha config
        · positivity
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ config : SourceMoleculeFibreConfig n,
        ∑ assignment : ↥S → ↥H,
          if ∀ r : ↥S, r.1 ∈ config (assignment r).1 then
            sourcePowerLawConfigWeight a n config else 0 :=
      Finset.sum_le_sum fun config hmem => hpoint config
    _ = ∑ assignment : ↥S → ↥H, sourceAssignmentMass a S H assignment := by
      rw [Finset.sum_comm]
      rfl
    _ = ∑ assignment : ↥S → ↥H,
        sourceAssignmentBlockProduct a S H assignment := by
      apply Finset.sum_congr rfl
      intro assignment hmem
      exact sourceAssignmentMass_eq_prod_blocks a ha hn S H assignment

/-- Coverage is bounded by a positive sum carrying one exact gateway factor
for every distinct catalyst identity used by an assignment. -/
theorem source_fixedCoverage_mass_le_range_weight_sum
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (S : Finset (Reaction n)) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ assignment : ↥S → ↥H,
        powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ^
          (sourceAssignmentRange S H assignment).card := by
  refine (source_fixedCoverage_mass_le_assignment_sum a ha hn H S).trans ?_
  apply Finset.sum_le_sum
  intro assignment hmem
  exact sourceAssignmentBlockProduct_le_gatewayHit_pow_range
    a ha hn S H assignment

end PowerLawSmallRAF
