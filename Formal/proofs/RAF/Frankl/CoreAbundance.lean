import proofs.RAF.Frankl.ReactionExtension

namespace RAF.Frankl

open RAF
open scoped Classical

variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

theorem core_exterior_reconstruct (U W : Finset R) :
    fromRestricted (toRestricted U W) ∪ (W \ U) = W := by
  ext r
  simp only [Finset.mem_union,mem_fromRestricted,mem_toRestricted,Finset.mem_sdiff]
  tauto

theorem core_extend_restrict (U T : Finset R) (hT : Disjoint T U)
    (S : Finset {r // r ∈ U}) :
    toRestricted U (fromRestricted S ∪ T) = S := by
  ext r
  have hn : r.1 ∉ T := fun ht => Finset.disjoint_left.mp hT ht r.2
  simp [hn]

omit [Fintype R] in
theorem core_extend_exterior (U T : Finset R) (hT : Disjoint T U)
    (S : Finset {r // r ∈ U}) :
    (fromRestricted S ∪ T) \ U = T := by
  ext r
  simp only [Finset.mem_sdiff,Finset.mem_union,mem_fromRestricted]
  constructor
  · rintro ⟨hr,hn⟩
    rcases hr with ⟨hu,_⟩ | ht
    · exact (hn hu).elim
    · exact ht
  · intro ht
    exact ⟨Or.inr ht,fun hu => Finset.disjoint_left.mp hT ht hu⟩

theorem core_restrict_injOn (Q : CRS M R) (C : Catalysis M R) (U T : Finset R) :
    ((fixedFamily Q C).filter (fun W => W \ U = T) : Set (Finset R)).InjOn
      (toRestricted U) := by
  intro A hA B hB heq
  have ha := (Finset.mem_filter.mp hA).2
  have hb := (Finset.mem_filter.mp hB).2
  have h := congrArg (fun S => fromRestricted S ∪ T) heq
  dsimp only at h
  rw [← ha,core_exterior_reconstruct] at h
  rw [ha,← hb,core_exterior_reconstruct] at h
  exact h

theorem core_fibre_image (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (hT : Disjoint T U) :
    ((fixedFamily Q C).filter (fun W => W \ U = T)).image (toRestricted U) =
      extensionFibre Q C U T := by
  ext S
  simp only [Finset.mem_image,Finset.mem_filter,extensionFibre,
    Finset.mem_powerset,Finset.subset_univ,true_and]
  constructor
  · rintro ⟨W,⟨hw,ht⟩,rfl⟩
    rw [← ht,core_exterior_reconstruct]
    exact hw
  · intro hs
    exact ⟨fromRestricted S ∪ T,⟨hs,core_extend_exterior U T hT S⟩,
      core_extend_restrict U T hT S⟩

/-- Arbitrary catalytic feedback and arbitrarily many non-food reactions are
allowed outside a viable elementary RAF. No projection premise is required. -/
theorem elementary_core_exists_abundant
    (Q : CRS M R) (C : Catalysis M R) (U : Finset R)
    (hU : IsRAF Q C U) (hE : ∀ r ∈ U, SeedReaction Q r) :
    ∃ r ∈ U, (fixedFamily Q C).card ≤
      2 * ((fixedFamily Q C).filter (fun W => r ∈ W)).card := by
  classical
  have hn : Nonempty {r // r ∈ U} := by
    obtain ⟨r,hr⟩ := hU.1
    exact ⟨⟨r,hr⟩⟩
  letI := hn
  apply Exists.elim (exists_frequency_of_fibre_average
    (fixedFamily Q C) (toRestricted U) (fun W => W \ U) ?_)
  · intro r hr
    exact ⟨r.1,r.2,by simpa using hr⟩
  · intro T
    by_cases hT : Disjoint T U
    · have h := extensionFibre_average Q C U T hU hE
      rw [← core_fibre_image Q C U T hT] at h
      rw [Finset.card_image_iff.mpr (core_restrict_injOn Q C U T),
        Finset.sum_image (core_restrict_injOn Q C U T)] at h
      exact h
    · have he : (fixedFamily Q C).filter (fun W => W \ U = T) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro W hw
        have ht := (Finset.mem_filter.mp hw).2
        apply hT
        rw [← ht]
        exact Finset.sdiff_disjoint
      simp [he]

theorem elementary_core_rafFixedFrankl
    (Q : CRS M R) (C : Catalysis M R) (U : Finset R)
    (hU : IsRAF Q C U) (hE : ∀ r ∈ U, SeedReaction Q r) :
    RAFFixedFrankl Q C := by
  intro _
  obtain ⟨r,_,hr⟩ := elementary_core_exists_abundant Q C U hU hE
  refine ⟨r,?_⟩
  have he : (∅ : Finset R) ∉ rafFamily Q C := by
    rw [mem_rafFamily]
    intro hh
    simpa using hh.1
  have hc : (fixedFamily Q C).card = (rafFamily Q C).card + 1 := by
    simp [fixedFamily,he]
  have hf : ((fixedFamily Q C).filter (fun W => r ∈ W)).card = frequency Q C r := by
    unfold frequency
    congr 1
    ext W
    simp [fixedFamily]
    aesop
  rwa [hc,hf] at hr

/-- Steel's stronger empty-inclusive target for a CRS with at most one reaction
whose reactants are not all food. The exceptional reaction may feed catalysts
back into any number of old reactions. -/
theorem one_nonfood_rafFixedFrankl
    (Q : CRS M R) (C : Catalysis M R) (g : R)
    (hE : ∀ r, r ≠ g → SeedReaction Q r) : RAFFixedFrankl Q C := by
  classical
  by_cases hcore : ∃ U : Finset R, IsRAF Q C U ∧ g ∉ U
  · obtain ⟨U,hu,hg⟩ := hcore
    apply elementary_core_rafFixedFrankl Q C U hu
    intro r hr
    apply hE r
    intro heq
    exact hg (heq ▸ hr)
  · intro hne
    refine ⟨g,?_⟩
    have hall : ∀ U ∈ rafFamily Q C, g ∈ U := by
      intro U hu
      by_contra hg
      exact hcore ⟨U,(mem_rafFamily Q C U).mp hu,hg⟩
    have hf : frequency Q C g = (rafFamily Q C).card := by
      unfold frequency
      congr 1
      ext S
      simp only [Finset.mem_filter]
      exact ⟨fun hh => hh.1,fun hs => ⟨hs,hall S hs⟩⟩
    rw [hf]
    have hp := Finset.card_pos.mpr hne
    omega

end RAF.Frankl
