import proofs.PowerLawSmallRAF.SourceOneFibreExtinction
import proofs.PowerLawSmallRAF.SourceSmallRAFUnionBound

namespace PowerLawSmallRAF

noncomputable section

open RAF RAF.Polymer RAF.Concrete

/-- A finite set of generated catalyst owners whose sampled fibres cover a
food-generated reaction scaffold.  This is the source-faithful combinatorial
core extracted from an arbitrary RAF. -/
def SourceOwnerCoverScaffold {n : Nat}
    (config : SourceMoleculeFibreConfig n) (H : Finset (Molecule n)) : Prop :=
  H.Nonempty ∧ ∃ S : Finset (Reaction n),
    S.Nonempty ∧ RevFoodGenerated (binaryPolymerCRS n 2) S ∧
      S ⊆ H.biUnion config ∧
      ∀ x ∈ H, ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k

def SourceIrredundantOwnerCover {n : Nat}
    (config : SourceMoleculeFibreConfig n) (S : Finset (Reaction n))
    (H : Finset (Molecule n)) : Prop :=
  S ⊆ H.biUnion config ∧
    ∀ x ∈ H, ∃ r ∈ S,
      r ∈ config x ∧ ∀ y ∈ H, y ≠ x → r ∉ config y

def SourceIrredundantOwnerScaffold {n : Nat}
    (config : SourceMoleculeFibreConfig n) (H : Finset (Molecule n)) : Prop :=
  H.Nonempty ∧ ∃ S : Finset (Reaction n),
    S.Nonempty ∧ RevFoodGenerated (binaryPolymerCRS n 2) S ∧
      SourceIrredundantOwnerCover config S H ∧
      ∀ x ∈ H, ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k

def SourceOwnerScaffoldOn {n : Nat}
    (config : SourceMoleculeFibreConfig n) (H : Finset (Molecule n))
    (S : Finset (Reaction n)) : Prop :=
  H.Nonempty ∧ S.Nonempty ∧ RevFoodGenerated (binaryPolymerCRS n 2) S ∧
    S ⊆ H.biUnion config ∧
    ∀ x ∈ H, ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k

/-- The genuinely cooperative remainder after singleton owner covers have
been removed.  The cutoff is on catalyst owners, not reactions. -/
def SourceMultiOwnerScaffold {n : Nat}
    (config : SourceMoleculeFibreConfig n) (m : Nat) : Prop :=
  ∃ H : Finset (Molecule n),
    2 ≤ H.card ∧ H.card ≤ m ∧ SourceIrredundantOwnerScaffold config H

noncomputable def sourceExistsMultiOwnerScaffoldWeight
    (a : ℝ) (n m : Nat) : ℝ := by
  classical
  exact ∑ config : SourceMoleculeFibreConfig n,
    if SourceMultiOwnerScaffold config m then
      sourcePowerLawConfigWeight a n config else 0

/-- Every finite fibre cover has an inclusion-minimal subcover; each retained
owner consequently has a private reaction. -/
theorem exists_irredundant_ownerSubcover {n : Nat}
    (config : SourceMoleculeFibreConfig n) {S : Finset (Reaction n)}
    {H : Finset (Molecule n)} (hSne : S.Nonempty)
    (hcover : S ⊆ H.biUnion config) :
    ∃ H' ⊆ H, H'.Nonempty ∧ SourceIrredundantOwnerCover config S H' := by
  classical
  let candidates := H.powerset.filter (fun K => S ⊆ K.biUnion config)
  have hcandidates : candidates.Nonempty := by
    exact ⟨H, by simp [candidates, hcover]⟩
  obtain ⟨H', hH'cand, hH'min⟩ :=
    candidates.exists_min_image Finset.card hcandidates
  have hH'sub : H' ⊆ H := Finset.mem_powerset.mp (Finset.mem_filter.mp hH'cand).1
  have hH'cover : S ⊆ H'.biUnion config := (Finset.mem_filter.mp hH'cand).2
  have hH'ne : H'.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hH'cover
    simp at hH'cover
    exact (Finset.nonempty_iff_ne_empty.mp hSne) hH'cover
  refine ⟨H', hH'sub, hH'ne, hH'cover, ?_⟩
  intro x hx
  by_contra hprivate
  push Not at hprivate
  have heraseCover : S ⊆ (H'.erase x).biUnion config := by
    intro r hr
    obtain ⟨y, hyH, hry⟩ := Finset.mem_biUnion.mp (hH'cover hr)
    by_cases hyx : y = x
    · subst y
      obtain ⟨z, hzH, hzx, hrz⟩ := hprivate r hr hry
      exact Finset.mem_biUnion.2 ⟨z, Finset.mem_erase.2 ⟨hzx, hzH⟩, hrz⟩
    · exact Finset.mem_biUnion.2 ⟨y, Finset.mem_erase.2 ⟨hyx, hyH⟩, hry⟩
  have heraseCand : H'.erase x ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨(Finset.erase_subset _ _).trans hH'sub, heraseCover⟩
  have hcard := hH'min (H'.erase x) heraseCand
  exact (not_lt_of_ge hcard) (Finset.card_erase_lt_of_mem hx)

/-- Every source RAF admits an owner cover no larger than its reaction set.
The owners are chosen from the literal autocatalysis witnesses, so every
owner is generated and its fibre contains the reaction assigned to it. -/
theorem source_revRAF_exists_ownerCover {n : Nat}
    {config : SourceMoleculeFibreConfig n} {S : Finset (Reaction n)}
    (hraf : IsRevRAF (binaryPolymerCRS n 2)
      (sourceCatalysisOfConfig config) S) :
    ∃ H : Finset (Molecule n),
      H.card ≤ S.card ∧ SourceOwnerCoverScaffold config H := by
  classical
  let owner : ↑S → Molecule n := fun r =>
    Classical.choose (hraf.2.2 r.1 r.2)
  have howner : ∀ r : ↑S, ∃ k,
      owner r ∈ revClosureAt (binaryPolymerCRS n 2) S k ∧
        r.1 ∈ config (owner r) := by
    intro r
    have hs := Classical.choose_spec (hraf.2.2 r.1 r.2)
    exact ⟨Classical.choose hs, (Classical.choose_spec hs).1,
      (Classical.choose_spec hs).2⟩
  let H : Finset (Molecule n) := Finset.univ.image owner
  refine ⟨H, ?_, ?_⟩
  · calc
      H.card ≤ (Finset.univ : Finset ↑S).card := Finset.card_image_le
      _ = S.card := by simp
  · have hSne : Nonempty ↑S := Finset.nonempty_coe_sort.mpr hraf.1
    have hHne : H.Nonempty := by
      let r : ↑S := Classical.choice hSne
      exact ⟨owner r, Finset.mem_image.2 ⟨r, Finset.mem_univ r, rfl⟩⟩
    refine ⟨hHne, S, hraf.1, hraf.2.1, ?_, ?_⟩
    · intro r hr
      let rS : ↑S := ⟨r, hr⟩
      have hoH : owner rS ∈ H :=
        Finset.mem_image.2 ⟨rS, Finset.mem_univ rS, rfl⟩
      exact Finset.mem_biUnion.2 ⟨owner rS, hoH, (howner rS).choose_spec.2⟩
    · intro x hx
      obtain ⟨r, hr, hownerEq⟩ := Finset.mem_image.mp hx
      subst x
      exact ⟨(howner r).choose, (howner r).choose_spec.1⟩

theorem source_revRAF_exists_irredundantOwnerScaffold {n : Nat}
    {config : SourceMoleculeFibreConfig n} {S : Finset (Reaction n)}
    (hraf : IsRevRAF (binaryPolymerCRS n 2)
      (sourceCatalysisOfConfig config) S) :
    ∃ H : Finset (Molecule n),
      H.card ≤ S.card ∧ SourceIrredundantOwnerScaffold config H := by
  obtain ⟨H, hHcard, hHne, T, hTne, hTfood, hTcover, hHgen⟩ :=
    source_revRAF_exists_ownerCover hraf
  obtain ⟨H', hH'sub, hH'ne, hH'irr⟩ :=
    exists_irredundant_ownerSubcover config hTne hTcover
  refine ⟨H', (Finset.card_le_card hH'sub).trans hHcard,
    hH'ne, T, hTne, hTfood, hH'irr, ?_⟩
  intro x hx
  exact hHgen x (hH'sub hx)

theorem source_ownerCoverScaffold_of_irredundant {n : Nat}
    {config : SourceMoleculeFibreConfig n} {H : Finset (Molecule n)}
    (h : SourceIrredundantOwnerScaffold config H) :
    SourceOwnerCoverScaffold config H := by
  obtain ⟨hHne, S, hSne, hfood, hcover, hgen⟩ := h
  exact ⟨hHne, S, hSne, hfood, hcover.1, hgen⟩

theorem sourceOwnerScaffoldOn_isRevRAF {n : Nat}
    {config : SourceMoleculeFibreConfig n} {H : Finset (Molecule n)}
    {S : Finset (Reaction n)} (h : SourceOwnerScaffoldOn config H S) :
    IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S := by
  refine ⟨h.2.1, h.2.2.1, ?_⟩
  intro r hr
  obtain ⟨x, hxH, hrx⟩ := Finset.mem_biUnion.mp (h.2.2.2.1 hr)
  obtain ⟨k, hxgen⟩ := h.2.2.2.2 x hxH
  exact ⟨x, k, hxgen, hrx⟩

theorem source_revRAF_exists_irredundantOwnerScaffold_on {n : Nat}
    {config : SourceMoleculeFibreConfig n} {S : Finset (Reaction n)}
    (hraf : IsRevRAF (binaryPolymerCRS n 2)
      (sourceCatalysisOfConfig config) S) :
    ∃ H : Finset (Molecule n), H.card ≤ S.card ∧
      SourceIrredundantOwnerCover config S H ∧
      SourceIrredundantOwnerScaffold config H ∧
      SourceOwnerScaffoldOn config H S := by
  classical
  let owner : ↑S → Molecule n := fun r =>
    Classical.choose (hraf.2.2 r.1 r.2)
  have howner : ∀ r : ↑S, ∃ k,
      owner r ∈ revClosureAt (binaryPolymerCRS n 2) S k ∧
        r.1 ∈ config (owner r) := by
    intro r
    have hs := Classical.choose_spec (hraf.2.2 r.1 r.2)
    exact ⟨Classical.choose hs, (Classical.choose_spec hs).1,
      (Classical.choose_spec hs).2⟩
  let H₀ : Finset (Molecule n) := Finset.univ.image owner
  have hcover : S ⊆ H₀.biUnion config := by
    intro r hr
    let rS : ↑S := ⟨r, hr⟩
    exact Finset.mem_biUnion.2 ⟨owner rS,
      Finset.mem_image.2 ⟨rS, Finset.mem_univ rS, rfl⟩,
      (howner rS).choose_spec.2⟩
  obtain ⟨H, hHH₀, hHne, hHirr⟩ :=
    exists_irredundant_ownerSubcover config hraf.1 hcover
  have hHcard : H.card ≤ S.card := by
    calc
      H.card ≤ H₀.card := Finset.card_le_card hHH₀
      _ ≤ (Finset.univ : Finset ↑S).card := Finset.card_image_le
      _ = S.card := by simp
  have hgen : ∀ x ∈ H, ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS n 2) S k := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (hHH₀ hx)
    exact ⟨(howner r).choose, (howner r).choose_spec.1⟩
  refine ⟨H, hHcard, hHirr,
    ⟨hHne, S, hraf.1, hraf.2.1, hHirr, hgen⟩,
    hHne, hraf.1, hraf.2.1, hHirr.1, hgen⟩

/-- For a minimum-cardinality RAF, the extracted irredundant owner cloud has
no cheaper scaffold.  Otherwise that scaffold would itself be a smaller RAF. -/
theorem source_minimalRevRAF_exists_minimalOwnerScaffold {n : Nat}
    {config : SourceMoleculeFibreConfig n} {S : Finset (Reaction n)}
    (hraf : IsRevRAF (binaryPolymerCRS n 2)
      (sourceCatalysisOfConfig config) S)
    (hminimal : ∀ T : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) T →
        S.card ≤ T.card) :
    ∃ H : Finset (Molecule n),
      H.card ≤ S.card ∧ SourceIrredundantOwnerScaffold config H ∧
        SourceOwnerScaffoldOn config H S ∧
        ∀ T : Finset (Reaction n), SourceOwnerScaffoldOn config H T →
          S.card ≤ T.card := by
  obtain ⟨H, hHcard, _hcover, hHirr, hSscaffold⟩ :=
    source_revRAF_exists_irredundantOwnerScaffold_on hraf
  exact ⟨H, hHcard, hHirr, hSscaffold,
    fun T hT => hminimal T (sourceOwnerScaffoldOn_isRevRAF hT)⟩

/-- A singleton owner cover is exactly a valid one-fibre scaffold. -/
theorem source_oneFibreScaffold_of_singleton_ownerCover {n : Nat}
    {config : SourceMoleculeFibreConfig n} {x : Molecule n}
    (h : SourceOwnerCoverScaffold config {x}) :
    SourceOneFibreScaffold config x := by
  obtain ⟨-, S, hSne, hfood, hcover, hgen⟩ := h
  refine ⟨S, ?_, hSne, hfood, ?_⟩
  · intro r hr
    have hm := hcover hr
    simpa using hm
  · simpa using hgen x (by simp)

/-- Every bounded RAF is witnessed either by a genuine one-owner scaffold or
by an irredundant cooperative owner cover with between two and `m` owners. -/
theorem source_boundedRevRAF_one_or_multiOwner {n m : Nat}
    {config : SourceMoleculeFibreConfig n}
    (h : ∃ S : Finset (Reaction n), S.card ≤ m ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S) :
    (∃ x : Molecule n, SourceOneFibreScaffold config x) ∨
      SourceMultiOwnerScaffold config m := by
  obtain ⟨S, hSm, hraf⟩ := h
  obtain ⟨H, hHS, hHirr⟩ :=
    source_revRAF_exists_irredundantOwnerScaffold hraf
  have hHm : H.card ≤ m := hHS.trans hSm
  by_cases hHone : H.card = 1
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hHone
    left
    exact ⟨x, source_oneFibreScaffold_of_singleton_ownerCover
      (source_ownerCoverScaffold_of_irredundant hHirr)⟩
  · right
    refine ⟨H, ?_, hHm, hHirr⟩
    have hHpos : 1 ≤ H.card := Finset.one_le_card.mpr hHirr.1
    omega

/-- Exact source-level reduction of the small-RAF event to the extinct
singleton event and the remaining irredundant cooperative event. -/
theorem sourceBoundedRevRAFProbability_le_one_add_multiOwner
    {n m : Nat} (a : ℝ) (ha : 1 < a) :
    sourceBoundedRevRAFProbability a n m ≤
      sourceExistsOneFibreScaffoldWeight a n +
        sourceExistsMultiOwnerScaffoldWeight a n m := by
  classical
  rw [sourceBoundedRevRAFProbability, sourceExistsOneFibreScaffoldWeight,
    sourceExistsMultiOwnerScaffoldWeight]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro config hconfig
  by_cases hraf : ∃ S : Finset (Reaction n), S.card ≤ m ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S
  · rw [if_pos hraf]
    rcases source_boundedRevRAF_one_or_multiOwner hraf with hone | hmulti
    · rw [if_pos hone]
      split_ifs
      · exact le_add_of_nonneg_right
          (sourcePowerLawConfigWeight_nonneg a n ha config)
      · simp
    · rw [if_pos hmulti]
      split_ifs
      · exact le_add_of_nonneg_left
          (sourcePowerLawConfigWeight_nonneg a n ha config)
      · simp
  · rw [if_neg hraf]
    exact add_nonneg (by
      split_ifs
      · exact sourcePowerLawConfigWeight_nonneg a n ha config
      · exact le_rfl) (by
      split_ifs
      · exact sourcePowerLawConfigWeight_nonneg a n ha config
      · exact le_rfl)

end

end PowerLawSmallRAF
