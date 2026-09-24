import proofs.PowerLawSmallRAF.GrowingCutoffExtinction

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

noncomputable def sourceSeedReactionFinset (n : Nat) : Finset (Reaction n) :=
  Finset.univ.filter fun r => RevSeedReaction (binaryPolymerCRS n 2) r

noncomputable def sourceGatewayOpenProbability (a : ℝ) (n : Nat) : ℝ := by
  classical
  exact ∑ config : SourceMoleculeFibreConfig n,
    if ∃ r ∈ sourceSeedReactionFinset n, ∃ x, r ∈ config x then
      sourcePowerLawConfigWeight a n config else 0

noncomputable def sourceFullRAFProbability (a : ℝ) (n : Nat) : ℝ :=
  sourceBoundedRevRAFProbability a n (Fintype.card (Reaction n))

/-- Exact seed-open law in the literal split-position source catalogue. -/
theorem sourceGatewayOpenProbability_exact
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) :
    sourceGatewayOpenProbability a n =
      1 - coverageMissProfile
        (cappedZipfDegreeMass a (sourceReactionCount n))
        (sourceReactionCount n) (sourceSeedReactionFinset n).card ^
          Fintype.card (Molecule n) := by
  classical
  let E : SourceMoleculeFibreConfig n → Prop := fun config =>
    ∃ r ∈ sourceSeedReactionFinset n, ∃ x, r ∈ config x
  let w := sourcePowerLawConfigWeight a n
  have htotal : (∑ config : SourceMoleculeFibreConfig n, w config) = 1 :=
    sum_sourcePowerLawConfigWeight_eq_one a n ha hn
  have hclosed := source_jointMiss_mass_eq_pow a ha hn
    (Finset.univ : Finset (Molecule n)) (sourceSeedReactionFinset n)
  have hclosed' : (∑ config : SourceMoleculeFibreConfig n,
      if ¬ E config then w config else 0) =
      coverageMissProfile
        (cappedZipfDegreeMass a (sourceReactionCount n))
        (sourceReactionCount n) (sourceSeedReactionFinset n).card ^
          Fintype.card (Molecule n) := by
    calc
      (∑ config : SourceMoleculeFibreConfig n,
          if ¬ E config then w config else 0) =
          ∑ config : SourceMoleculeFibreConfig n,
            if ∀ x : ↥(Finset.univ : Finset (Molecule n)),
                Disjoint (config x) (sourceSeedReactionFinset n) then
              sourcePowerLawConfigWeight a n config else 0 := by
        apply Finset.sum_congr rfl
        intro config hconfig
        have heq : (¬ E config) ↔
            ∀ x : ↥(Finset.univ : Finset (Molecule n)),
              Disjoint (config x) (sourceSeedReactionFinset n) := by
          constructor
          · intro h x
            rw [Finset.disjoint_left]
            intro r hrx hrseed
            exact h ⟨r, hrseed, x.1, hrx⟩
          · intro h hex
            obtain ⟨r, hrseed, x, hrx⟩ := hex
            exact (Finset.disjoint_left.mp
              (h ⟨x, Finset.mem_univ x⟩)) hrx hrseed
        simp only [w]
        rw [if_congr heq rfl rfl]
      _ = _ := by simpa using hclosed
  have hsplit :
      (∑ config : SourceMoleculeFibreConfig n,
          if E config then w config else 0) +
        (∑ config : SourceMoleculeFibreConfig n,
          if ¬ E config then w config else 0) = 1 := by
    rw [← htotal]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro config hconfig
    by_cases hE : E config <;> simp [hE]
  rw [sourceGatewayOpenProbability]
  change (∑ config : SourceMoleculeFibreConfig n,
    if E config then w config else 0) = _
  linarith

theorem sourceFullRAFProbability_le_gatewayOpen
    {n : Nat} (a : ℝ) (ha : 1 < a) :
    sourceFullRAFProbability a n ≤ sourceGatewayOpenProbability a n := by
  classical
  rw [sourceFullRAFProbability, sourceBoundedRevRAFProbability,
    sourceGatewayOpenProbability]
  apply Finset.sum_le_sum
  intro config hconfig
  split_ifs with hraf hopen
  · exact le_rfl
  · exfalso
    obtain ⟨S, _hScard, hS⟩ := hraf
    have hseed := rev_raf_implies_seedOpen (binaryPolymerCRS n 2)
      (sourceCatalysisOfConfig config) S hS
    obtain ⟨r, hrseed, x, hx⟩ := hseed
    have hrmem : r ∈ sourceSeedReactionFinset n := by
      simp [sourceSeedReactionFinset, hrseed]
    exact hopen ⟨r, hrmem, x, hx⟩
  · exact sourcePowerLawConfigWeight_nonneg a n ha config
  · exact le_rfl

noncomputable def sourceGatewayConditionedBulkProbability
    (a : ℝ) (n : Nat) : ℝ :=
  sourceFullRAFProbability a n / sourceGatewayOpenProbability a n

/-- Exact source boundary--bulk factorization.  This is algebraic conditioning,
not an independence assertion. -/
theorem sourceFullRAFProbability_gateway_factorization
    {a : ℝ} {n : Nat} (hopen : sourceGatewayOpenProbability a n ≠ 0) :
    sourceFullRAFProbability a n =
      sourceGatewayOpenProbability a n *
        sourceGatewayConditionedBulkProbability a n := by
  rw [sourceGatewayConditionedBulkProbability]
  field_simp

end PowerLawSmallRAF
