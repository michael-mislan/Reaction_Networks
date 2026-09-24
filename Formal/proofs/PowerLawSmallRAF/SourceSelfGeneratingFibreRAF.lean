import proofs.PowerLawSmallRAF.SourceGatewayFactorization

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- A literal source fibre is self-generating when it is nonempty,
food-generated in the reversible polymer CRS, and generates its owner. -/
def SourceSelfGeneratingFibre {n : Nat}
    (config : SourceMoleculeFibreConfig n) (x : Molecule n) : Prop :=
  (config x).Nonempty ∧
    RevFoodGenerated (binaryPolymerCRS n 2) (config x) ∧
    ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) (config x) k

/-- Any nonempty food-generated scaffold lying in one molecule's fibre and
generating that molecule is a reversible RAF. -/
theorem source_fibreScaffold_isRevRAF {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    {S : Finset (Reaction n)} (hsub : S ⊆ config x) (hne : S.Nonempty)
    (hfood : RevFoodGenerated (binaryPolymerCRS n 2) S)
    (hgen : ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k) :
    IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S := by
  obtain ⟨k, hx⟩ := hgen
  refine ⟨hne, hfood, ?_⟩
  intro r hr
  exact ⟨x, k, hx, hsub hr⟩

/-- A self-generating molecule fibre is itself a reversible RAF.  This is the
deterministic bridge audited by the exact maximal-RAF experiment. -/
theorem source_selfGeneratingFibre_isRevRAF {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    (hself : SourceSelfGeneratingFibre config x) :
    IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config)
      (config x) := by
  rcases hself with ⟨hne, hfood, hgen⟩
  exact source_fibreScaffold_isRevRAF Finset.Subset.rfl hne hfood hgen

/-- A one-fibre scaffold yields a RAF whose size is bounded by that fibre's
sampled source degree. -/
theorem source_fibreScaffold_card_le_degree {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    {S : Finset (Reaction n)} (hsub : S ⊆ config x) (hne : S.Nonempty)
    (hfood : RevFoodGenerated (binaryPolymerCRS n 2) S)
    (hgen : ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k) :
    S.card ≤ (config x).card ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S :=
  ⟨Finset.card_le_card hsub,
    source_fibreScaffold_isRevRAF hsub hne hfood hgen⟩

/-- Every one-fibre scaffold pays the literal finite seed cost inside that
same fibre.  This is the obstruction missed by finite `c/n` closure plots. -/
theorem source_fibreScaffold_has_internal_seed {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    {S : Finset (Reaction n)} (hsub : S ⊆ config x) (hne : S.Nonempty)
    (hfood : RevFoodGenerated (binaryPolymerCRS n 2) S) :
    ∃ r ∈ sourceSeedReactionFinset n, r ∈ config x := by
  obtain ⟨r, hrS, hrseed⟩ :=
    exists_rev_seed_of_foodGenerated (binaryPolymerCRS n 2) S hne hfood
  exact ⟨r, by simp [sourceSeedReactionFinset, hrseed], hsub hrS⟩

theorem source_selfGeneratingFibre_has_internal_seed {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    (hself : SourceSelfGeneratingFibre config x) :
    ∃ r ∈ sourceSeedReactionFinset n, r ∈ config x := by
  exact source_fibreScaffold_has_internal_seed Finset.Subset.rfl
    hself.1 hself.2.1

/-- There are at most 68 literal split-position seed channels, uniformly in
the polymer horizon. -/
theorem card_sourceSeedReactionFinset_le_68 (n : Nat) :
    (sourceSeedReactionFinset n).card ≤ 68 := by
  classical
  let f : ↥(sourceSeedReactionFinset n) → PolymerSeedReaction n 2 :=
    fun r => ⟨r.1, (Finset.mem_filter.mp r.2).2⟩
  have hinj : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    exact congrArg (fun z : PolymerSeedReaction n 2 => z.1) hrs
  calc
    (sourceSeedReactionFinset n).card =
        Fintype.card ↥(sourceSeedReactionFinset n) := by simp
    _ ≤ Fintype.card (PolymerSeedReaction n 2) :=
      Fintype.card_le_of_injective f hinj
    _ ≤ 68 := card_polymerSeedReaction_le_68 n

/-- Existence of one self-generating fibre supplies an actual source RAF,
without a coverage-only or independence relaxation. -/
theorem exists_source_revRAF_of_exists_selfGeneratingFibre {n : Nat}
    {config : SourceMoleculeFibreConfig n}
    (hself : ∃ x, SourceSelfGeneratingFibre config x) :
    ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S := by
  obtain ⟨x, hx⟩ := hself
  exact ⟨config x, source_selfGeneratingFibre_isRevRAF hx⟩

/-- The resulting RAF has no more reactions than the owner fibre: indeed the
canonical witness is the fibre itself. -/
theorem exists_source_revRAF_card_le_fibre_of_selfGenerating {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    (hself : SourceSelfGeneratingFibre config x) :
    ∃ S : Finset (Reaction n),
      S.card ≤ (config x).card ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S := by
  exact ⟨config x, le_rfl, source_selfGeneratingFibre_isRevRAF hself⟩

end PowerLawSmallRAF
