import proofs.RAFInteriorRealizability.MarkerProvenance

namespace RAFInteriorRealizability

open RAF RAF.Frankl MarkerMolecule

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

namespace MarkerSource

theorem foodGenerated_insert_of_inputs_reachable
    (A : AntimatroidData E) {S : Finset E} {e : E}
    (hfg : FoodGenerated (crs A) S)
    (hreaches : ∀ x ∈ (crs A).inputs e,
      ∃ k, x ∈ closureAt (crs A) S k) :
    FoodGenerated (crs A) (insert e S) := by
  intro r hr
  rcases Finset.mem_insert.mp hr with hre | hrS
  · subst r
    obtain ⟨k, hk⟩ := finite_inputs_reach_one_stage A S ((crs A).inputs e) hreaches
    exact ⟨k, fun x hx => closureAt_mono_reactions (crs A)
      (Finset.subset_insert e S) k (hk hx)⟩
  · obtain ⟨k, hk⟩ := hfg r hrS
    exact ⟨k, fun x hx => closureAt_mono_reactions (crs A)
      (Finset.subset_insert e S) k (hk hx)⟩

theorem foodGenerated_of_mem (A : AntimatroidData E) :
    ∀ S : Finset E, S ∈ A.family → FoodGenerated (crs A) S := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih hAS
  by_cases hzero : S = ∅
  · subst S
    exact foodGenerated_empty (crs A)
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    obtain ⟨e, heS, heraseA⟩ := A.accessible hAS hne
    have hproper : S.erase e ⊂ S := Finset.erase_ssubset heS
    have hfgErase : FoodGenerated (crs A) (S.erase e) :=
      ih (S.erase e) hproper heraseA
    have hreach : ∀ x ∈ (crs A).inputs e,
        ∃ k, x ∈ closureAt (crs A) (S.erase e) k := by
      intro x hx
      cases x with
      | food => exact ⟨0, by simp [closureAt, crs]⟩
      | catalyst u => simp [crs] at hx
      | marker target B =>
          simp [crs] at hx
          rcases hx with ⟨htarget, hB⟩
          subst target
          have hfix : A.toUnionClosedData.interior S = S :=
            (A.toUnionClosedData.fixed_iff_mem S).2 hAS
          have heInterior : e ∈ A.toUnionClosedData.interior S := by
            rw [hfix]
            exact heS
          have hhit :=
            (A.toUnionClosedData.mem_interior_iff_hits_blockers heS).1
              heInterior B hB
          obtain ⟨j, hjS, hjB⟩ := Finset.not_disjoint_iff.mp hhit
          have hje : j ≠ e := by
            intro h
            subst j
            exact hB.1 hjB
          have hjErase : j ∈ S.erase e := Finset.mem_erase.mpr ⟨hje, hjS⟩
          exact marker_reachable_of_hit A hfgErase hjErase hjB hB
    have hins := foodGenerated_insert_of_inputs_reachable A hfgErase hreach
    simpa [Finset.insert_erase heS] using hins

theorem mem_of_foodGenerated (A : AntimatroidData E) :
    ∀ S : Finset E, FoodGenerated (crs A) S → S ∈ A.family := by
  intro S
  refine Finset.strongInductionOn S ?_
  intro S ih hfg
  by_cases hzero : S = ∅
  · subst S
    exact A.empty_mem
  · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    obtain ⟨e, heS, hfgErase⟩ := foodGenerated_accessible (crs A) hne hfg
    have hproper : S.erase e ⊂ S := Finset.erase_ssubset heS
    have heraseA : S.erase e ∈ A.family := ih (S.erase e) hproper hfgErase
    have hfixErase : A.toUnionClosedData.interior (S.erase e) = S.erase e :=
      (A.toUnionClosedData.fixed_iff_mem (S.erase e)).2 heraseA
    obtain ⟨k, hk⟩ := hfg e heS
    have hhit : ∀ B : Finset E, A.toUnionClosedData.IsBlocker e B →
        ¬ Disjoint S B := by
      intro B hB
      have hmarkerInput : marker e B ∈ (crs A).inputs e := by
        classical
        simp [crs, hB]
      obtain ⟨-, j, hjB, hjS⟩ := marker_origin A S (hk hmarkerInput)
      exact Finset.not_disjoint_iff.2 ⟨j, hjS, hjB⟩
    have heInterior : e ∈ A.toUnionClosedData.interior S :=
      (A.toUnionClosedData.mem_interior_iff_hits_blockers heS).2 hhit
    have hfix : A.toUnionClosedData.interior S = S := by
      apply Finset.Subset.antisymm (A.toUnionClosedData.interior_subset S)
      intro x hxS
      by_cases hxe : x = e
      · simpa [hxe] using heInterior
      · have hxErase : x ∈ S.erase e := Finset.mem_erase.mpr ⟨hxe, hxS⟩
        have hxInteriorErase : x ∈ A.toUnionClosedData.interior (S.erase e) := by
          rw [hfixErase]
          exact hxErase
        exact A.toUnionClosedData.interior_mono (Finset.erase_subset e S)
          hxInteriorErase
    exact (A.toUnionClosedData.fixed_iff_mem S).1 hfix

/-- Exact abstract converse: the literal marker CRS has precisely the supplied
antimatroid as its food-generated family. -/
theorem foodGenerated_iff_mem (A : AntimatroidData E) (S : Finset E) :
    FoodGenerated (crs A) S ↔ S ∈ A.family :=
  ⟨mem_of_foodGenerated A S, foodGenerated_of_mem A S⟩

end MarkerSource

end RAFInteriorRealizability
