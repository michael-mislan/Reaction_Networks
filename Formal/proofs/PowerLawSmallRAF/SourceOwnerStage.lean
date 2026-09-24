import proofs.PowerLawSmallRAF.SourceOwnerCoverScaffold

namespace PowerLawSmallRAF

noncomputable section

open RAF RAF.Polymer RAF.Concrete

universe uM uR

variable {M : Type uM} {R : Type uR} [DecidableEq M] [DecidableEq R]

omit [DecidableEq R] in
/-- Reversible closure only grows with time. -/
theorem revClosureAt_mono_time (Q : ReversibleCRS M R) (S : Finset R) :
    Monotone (revClosureAt Q S) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ j _ ih =>
      exact ih.trans (by
        intro x hx
        simp only [revClosureAt, revClosureStep, Finset.mem_union]
        exact Or.inl hx)

omit [DecidableEq R] in
/-- Reversible closure is monotone in the permitted reaction set. -/
theorem revClosureAt_mono_reaction_set (Q : ReversibleCRS M R)
    {S T : Finset R} (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k := by
  intro k
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
      exact HordijkSteelThreshold.revClosureStep_mono Q hST ih

/-- The portion of a source owner cloud enabled in at least one orientation by
depth `K` of the complete cloud closure. -/
noncomputable def sourceOwnerStage {n : Nat}
    (config : SourceMoleculeFibreConfig n) (H : Finset (Molecule n))
    (K : Nat) : Finset (Reaction n) :=
  (H.biUnion config).filter fun r =>
    RevEnabledLhs (binaryPolymerCRS n 2)
        (revClosureAt (binaryPolymerCRS n 2) (H.biUnion config) K) r ∨
      RevEnabledRhs (binaryPolymerCRS n 2)
        (revClosureAt (binaryPolymerCRS n 2) (H.biUnion config) K) r

omit [DecidableEq R] in
theorem revClosureStep_eq_of_revEnabled_subset
    (Q : ReversibleCRS M R) {S T : Finset R} {A : Finset M}
    (hTS : T ⊆ S)
    (hST : ∀ r ∈ S,
      (RevEnabledLhs Q A r ∨ RevEnabledRhs Q A r) → r ∈ T) :
    revClosureStep Q S A = revClosureStep Q T A := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
    rcases hx with hx | ⟨r, hrS, hxr⟩
    · exact Or.inl hx
    · by_cases hl : RevEnabledLhs Q A r
      · exact Or.inr ⟨r, hST r hrS (Or.inl hl), by simpa [hl] using hxr⟩
      · by_cases hr : RevEnabledRhs Q A r
        · exact Or.inr ⟨r, hST r hrS (Or.inr hr), by simpa [hl, hr] using hxr⟩
        · simp [hl, hr] at hxr
  · exact HordijkSteelThreshold.revClosureStep_mono Q hTS
      (fun _ hx => hx)

/-- Restricting the owner cloud to its depth-`K` enabled stage preserves the
complete-cloud closure through depth `K+1`. -/
theorem revClosureAt_sourceOwnerStage_eq_of_le {n : Nat}
    (config : SourceMoleculeFibreConfig n) (H : Finset (Molecule n))
    (K j : Nat) (hj : j ≤ K + 1) :
    revClosureAt (binaryPolymerCRS n 2) (sourceOwnerStage config H K) j =
      revClosureAt (binaryPolymerCRS n 2) (H.biUnion config) j := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
      have hjK : j ≤ K := by omega
      have ih' := ih (by omega : j ≤ K + 1)
      simp only [revClosureAt, ih']
      apply Eq.symm
      apply revClosureStep_eq_of_revEnabled_subset
      · intro r hr
        exact (Finset.mem_filter.mp hr).1
      · intro r hrCloud hrEnabled
        apply Finset.mem_filter.mpr
        refine ⟨hrCloud, ?_⟩
        rcases hrEnabled with hl | hr
        · exact Or.inl (fun x hx =>
            revClosureAt_mono_time _ _ hjK (hl hx))
        · exact Or.inr (fun x hx =>
            revClosureAt_mono_time _ _ hjK (hr hx))

/-- A nonempty enabled stage which generates all its owners is a scaffold on
those same owners. -/
theorem sourceOwnerStage_is_scaffold {n K : Nat}
    {config : SourceMoleculeFibreConfig n} {H : Finset (Molecule n)}
    (hH : H.Nonempty)
    (hstage : (sourceOwnerStage config H K).Nonempty)
    (hgen : ∀ x ∈ H,
      x ∈ revClosureAt (binaryPolymerCRS n 2) (H.biUnion config) K) :
    SourceOwnerScaffoldOn config H (sourceOwnerStage config H K) := by
  classical
  let Q := binaryPolymerCRS n 2
  have hclosureK :
      revClosureAt Q (sourceOwnerStage config H K) K =
        revClosureAt Q (H.biUnion config) K :=
    revClosureAt_sourceOwnerStage_eq_of_le config H K K (by omega)
  refine ⟨hH, hstage, ?_, ?_, ?_⟩
  · intro r hrStage
    refine ⟨K + 1, ?_⟩
    intro y hy
    have henabled := (Finset.mem_filter.mp hrStage).2
    simp only [revClosureAt, revClosureStep, Finset.mem_union,
      Finset.mem_biUnion]
    rcases Finset.mem_union.mp hy with hyL | hyR
    · rcases henabled with hl | hr
      · exact Or.inl (by rw [hclosureK]; exact hl hyL)
      · have hr' : RevEnabledRhs (binaryPolymerCRS n 2)
            (revClosureAt (binaryPolymerCRS n 2)
              (sourceOwnerStage config H K) K) r := by
          rw [hclosureK]
          exact hr
        refine Or.inr ⟨r, hrStage, Or.inr ?_⟩
        simpa only [if_pos hr'] using hyL
    · rcases henabled with hl | hr
      · have hl' : RevEnabledLhs (binaryPolymerCRS n 2)
            (revClosureAt (binaryPolymerCRS n 2)
              (sourceOwnerStage config H K) K) r := by
          rw [hclosureK]
          exact hl
        refine Or.inr ⟨r, hrStage, Or.inl ?_⟩
        simpa only [if_pos hl'] using hyR
      · exact Or.inl (by rw [hclosureK]; exact hr hyR)
  · intro r hr
    exact (Finset.mem_filter.mp hr).1
  · intro x hx
    exact ⟨K, by rw [hclosureK]; exact hgen x hx⟩

/-- Minimum-support RAFs force every nonempty same-owner enabled stage which
generates the owners to contain at least as many reactions. -/
theorem minimal_support_le_sourceOwnerStage {n K : Nat}
    {config : SourceMoleculeFibreConfig n} {H : Finset (Molecule n)}
    {S : Finset (Reaction n)}
    (hminimal : ∀ T : Finset (Reaction n),
      SourceOwnerScaffoldOn config H T → S.card ≤ T.card)
    (hH : H.Nonempty)
    (hstage : (sourceOwnerStage config H K).Nonempty)
    (hgen : ∀ x ∈ H,
      x ∈ revClosureAt (binaryPolymerCRS n 2) (H.biUnion config) K) :
    S.card ≤ (sourceOwnerStage config H K).card :=
  hminimal _ (sourceOwnerStage_is_scaffold hH hstage hgen)

/-- Every owner scaffold admits one common depth whose complete owner-cloud
stage is nonempty and is again a scaffold on exactly the same owners. -/
theorem exists_sourceOwnerStage_scaffold_of_scaffoldOn {n : Nat}
    {config : SourceMoleculeFibreConfig n} {H : Finset (Molecule n)}
    {S : Finset (Reaction n)} (h : SourceOwnerScaffoldOn config H S) :
    ∃ K, SourceOwnerScaffoldOn config H (sourceOwnerStage config H K) := by
  classical
  obtain ⟨r, hrS⟩ := h.2.1
  obtain ⟨kr, hkr⟩ := h.2.2.1 r hrS
  let ownerDepth : Molecule n → Nat := fun x =>
    if hx : x ∈ H then Classical.choose (h.2.2.2.2 x hx) else 0
  have hownerDepth : ∀ x ∈ H,
      x ∈ revClosureAt (binaryPolymerCRS n 2) S (ownerDepth x) := by
    intro x hx
    simp only [ownerDepth, dif_pos hx]
    exact Classical.choose_spec (h.2.2.2.2 x hx)
  let K := kr + ∑ x ∈ H, ownerDepth x
  have hkrK : kr ≤ K := by simp [K]
  have hgenCloud : ∀ x ∈ H,
      x ∈ revClosureAt (binaryPolymerCRS n 2) (H.biUnion config) K := by
    intro x hx
    have hdepthSum : ownerDepth x ≤ ∑ y ∈ H, ownerDepth y :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
    have hdepthK : ownerDepth x ≤ K := by
      simp only [K]
      omega
    exact revClosureAt_mono_time _ _ hdepthK
      (revClosureAt_mono_reaction_set _ h.2.2.2.1 _ (hownerDepth x hx))
  have hrStage : r ∈ sourceOwnerStage config H K := by
    apply Finset.mem_filter.mpr
    refine ⟨h.2.2.2.1 hrS, Or.inl ?_⟩
    intro y hy
    have hyS : y ∈ revClosureAt (binaryPolymerCRS n 2) S kr :=
      hkr (Finset.mem_union_left _ hy)
    exact revClosureAt_mono_time _ _ hkrK
      (revClosureAt_mono_reaction_set _ h.2.2.2.1 kr hyS)
  exact ⟨K, sourceOwnerStage_is_scaffold h.1 ⟨r, hrStage⟩ hgenCloud⟩

/-- The structural small-owner alternative for a minimum RAF: some complete
owner-cloud stage already contains at least the minimum RAF's reaction count. -/
theorem minimal_scaffold_has_large_ownerStage {n : Nat}
    {config : SourceMoleculeFibreConfig n} {H : Finset (Molecule n)}
    {S : Finset (Reaction n)}
    (hscaffold : SourceOwnerScaffoldOn config H S)
    (hminimal : ∀ T : Finset (Reaction n),
      SourceOwnerScaffoldOn config H T → S.card ≤ T.card) :
    ∃ K, S.card ≤ (sourceOwnerStage config H K).card := by
  obtain ⟨K, hstage⟩ :=
    exists_sourceOwnerStage_scaffold_of_scaffoldOn hscaffold
  exact ⟨K, hminimal _ hstage⟩

end

end PowerLawSmallRAF
