import proofs.PowerLawSmallRAF.CoverageAssignmentEnvelope

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- Two-stratum range bound for all functions between finite types.  Constant
functions pay one factor `p`; every nonconstant function pays at least two. -/
theorem sum_pow_card_range_le_one_add_two
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ f : α → β, p ^ (Finset.univ.image f).card) ≤
      (Fintype.card β : ℝ) * p +
        ((Fintype.card β) ^ (Fintype.card α) : Nat) * p ^ 2 := by
  classical
  let one : Finset (α → β) := Finset.univ.filter fun f =>
    (Finset.univ.image f).card = 1
  let r₀ : α := Classical.choice inferInstance
  have hcardOne : one.card ≤ Fintype.card β := by
    apply Finset.card_le_card_of_injOn (fun f : α → β => f r₀)
    · intro f hf
      exact Finset.mem_univ _
    · intro f hf g hg heq
      apply funext
      intro r
      have hfcard : (Finset.univ.image f).card ≤ 1 := by
        have := (Finset.mem_filter.mp hf).2
        omega
      have hgcard : (Finset.univ.image g).card ≤ 1 := by
        have := (Finset.mem_filter.mp hg).2
        omega
      have hfr : f r ∈ Finset.univ.image f :=
        Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
      have hf0 : f r₀ ∈ Finset.univ.image f :=
        Finset.mem_image.mpr ⟨r₀, Finset.mem_univ _, rfl⟩
      have hgr : g r ∈ Finset.univ.image g :=
        Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
      have hg0 : g r₀ ∈ Finset.univ.image g :=
        Finset.mem_image.mpr ⟨r₀, Finset.mem_univ _, rfl⟩
      calc
        f r = f r₀ := (Finset.card_le_one.mp hfcard _ hfr _ hf0)
        _ = g r₀ := heq
        _ = g r := (Finset.card_le_one.mp hgcard _ hgr _ hg0).symm
  have hone : (∑ f ∈ one, p ^ (Finset.univ.image f).card) =
      (one.card : ℝ) * p := by
    calc
      (∑ f ∈ one, p ^ (Finset.univ.image f).card) =
          ∑ _f ∈ one, p := by
        apply Finset.sum_congr rfl
        intro f hf
        rw [(Finset.mem_filter.mp hf).2, pow_one]
      _ = (one.card : ℝ) * p := by simp
  have hnotOne : (∑ f ∈ (Finset.univ : Finset (α → β)).filter
      (fun f => ¬(Finset.univ.image f).card = 1),
        p ^ (Finset.univ.image f).card) ≤
      (((Finset.univ : Finset (α → β)).filter
        (fun f => ¬(Finset.univ.image f).card = 1)).card : ℝ) * p ^ 2 := by
    calc
      (∑ f ∈ (Finset.univ : Finset (α → β)).filter
        (fun f => ¬(Finset.univ.image f).card = 1),
          p ^ (Finset.univ.image f).card) ≤
        ∑ _f ∈ (Finset.univ : Finset (α → β)).filter
          (fun f => ¬(Finset.univ.image f).card = 1), p ^ 2 := by
        apply Finset.sum_le_sum
        intro f hf
        have hne := (Finset.mem_filter.mp hf).2
        have hpos : 0 < (Finset.univ.image f).card :=
          Finset.card_pos.mpr ⟨f r₀,
            Finset.mem_image.mpr ⟨r₀, Finset.mem_univ _, rfl⟩⟩
        have htwo : 2 ≤ (Finset.univ.image f).card := by omega
        exact pow_le_pow_of_le_one hp0 hp1 htwo
      _ = (((Finset.univ : Finset (α → β)).filter
          (fun f => ¬(Finset.univ.image f).card = 1)).card : ℝ) * p ^ 2 := by
        simp
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (α → β))
    (fun f => (Finset.univ.image f).card = 1)
    (fun f => p ^ (Finset.univ.image f).card)
  rw [show (Finset.univ.filter fun f : α → β =>
    (Finset.univ.image f).card = 1) = one by rfl] at hsplit
  calc
    (∑ f : α → β, p ^ (Finset.univ.image f).card) =
        (∑ f ∈ one, p ^ (Finset.univ.image f).card) +
        ∑ f ∈ (Finset.univ : Finset (α → β)).filter
          (fun f => ¬(Finset.univ.image f).card = 1),
            p ^ (Finset.univ.image f).card := hsplit.symm
    _ ≤ (one.card : ℝ) * p +
        (((Finset.univ : Finset (α → β)).filter
          (fun f => ¬(Finset.univ.image f).card = 1)).card : ℝ) * p ^ 2 := by
      rw [hone]
      exact add_le_add le_rfl hnotOne
    _ ≤ (Fintype.card β : ℝ) * p +
        (Fintype.card (α → β) : ℝ) * p ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardOne) hp0
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg p)
        exact_mod_cast Finset.card_filter_le
          (Finset.univ : Finset (α → β))
          (fun f => ¬(Finset.univ.image f).card = 1)
    _ = (Fintype.card β : ℝ) * p +
        ((Fintype.card β) ^ (Fintype.card α) : Nat) * p ^ 2 := by
      rw [Fintype.card_fun]

theorem source_gatewayHit_nonneg_le_one
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (r : Reaction n) :
    0 ≤ powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ∧
      powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ≤ 1 := by
  classical
  let w : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  have hmass : ∀ A, 0 ≤ w A := fun A =>
    subsetDegreeWeight_nonneg _
      (fun d => cappedZipfDegreeMass_nonneg a _ d (by
        rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
        nlinarith [rpowTail_nonneg a 2])) A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hwsum : ∑ A : Finset (Reaction n), w A = 1 := by
    dsimp [w]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  rw [← source_oneFibre_incidence_mass_eq_gatewayHit a ha hn r]
  constructor
  · apply Finset.sum_nonneg
    intro A hA
    split_ifs
    · exact hmass A
    · positivity
  · calc
      (∑ A : Finset (Reaction n), if r ∈ A then w A else 0) ≤
          ∑ A : Finset (Reaction n), w A := by
        apply Finset.sum_le_sum
        intro A hA
        by_cases hr : r ∈ A
        · rw [if_pos hr]
        · rw [if_neg hr]
          exact hmass A
      _ = 1 := hwsum

theorem card_sourceAssignmentRange_eq_card_range
    {n : Nat} (S : Finset (Reaction n)) (H : Finset (Molecule n))
    (assignment : ↥S → ↥H) :
    (sourceAssignmentRange S H assignment).card =
      (Finset.univ.image assignment).card := by
  classical
  have heq : sourceAssignmentRange S H assignment =
      (Finset.univ.image assignment).image Subtype.val := by
    ext x
    constructor
    · intro hx
      rw [sourceAssignmentRange, Finset.mem_image] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      rw [Finset.mem_image]
      exact ⟨assignment r,
        Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, rfl⟩
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Finset.mem_image] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      rw [sourceAssignmentRange, Finset.mem_image]
      exact ⟨r, Finset.mem_univ _, rfl⟩
  rw [heq, Finset.card_image_of_injective]
  exact Subtype.val_injective

/-- The source coverage event obeys a concrete two-stratum estimate: constant
assignments pay one gateway factor and every nonconstant assignment pays two. -/
theorem source_fixedCoverage_mass_le_one_add_two
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (H : Finset (Molecule n)) (S : Finset (Reaction n)) (hne : S.Nonempty) :
    (∑ config : SourceMoleculeFibreConfig n,
      if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
        sourcePowerLawConfigWeight a n config else 0) ≤
      (H.card : ℝ) *
          powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 +
        ((H.card ^ S.card : Nat) : ℝ) *
          powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ^ 2 := by
  classical
  obtain ⟨r, hrS⟩ := hne
  letI : Nonempty ↥S := ⟨⟨r, hrS⟩⟩
  let p := powerLawMoleculeGatewayHit a (sourceReactionCount n) 1
  have hp := source_gatewayHit_nonneg_le_one a ha hn r
  refine (source_fixedCoverage_mass_le_range_weight_sum a ha hn H S).trans ?_
  have hcount := sum_pow_card_range_le_one_add_two
    (α := ↥S) (β := ↥H) p hp.1 hp.2
  have hrange : (∑ assignment : ↥S → ↥H,
      p ^ (sourceAssignmentRange S H assignment).card) =
      ∑ assignment : ↥S → ↥H,
        p ^ (Finset.univ.image assignment).card := by
    apply Finset.sum_congr rfl
    intro assignment hmem
    rw [card_sourceAssignmentRange_eq_card_range S H assignment]
  rw [hrange]
  simpa [p] using hcount

end PowerLawSmallRAF
