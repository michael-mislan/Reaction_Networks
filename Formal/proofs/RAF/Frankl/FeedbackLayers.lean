import proofs.RAF.Frankl.ProjectionCriterion

namespace RAF.Frankl

open RAF
open scoped Classical

variable {R : Type*} [DecidableEq R]

/-- Rows omitting the exceptional reaction. -/
noncomputable def absentLayer (F : Finset (Finset R)) (g : R) : Finset (Finset R) :=
  F.filter fun S => g ∉ S

/-- Exact projected rows containing the exceptional reaction. -/
noncomputable def presentLayer (F : Finset (Finset R)) (g : R) : Finset (Finset R) :=
  (F.filter fun S => g ∈ S).image fun S => S.erase g

theorem erase_injective_on_present (F : Finset (Finset R)) (g : R) :
    (F.filter (fun S => g ∈ S) : Set (Finset R)).InjOn (fun S => S.erase g) := by
  intro S hs T ht he
  have h := congrArg (insert g) he
  simpa only [Finset.insert_erase (Finset.mem_filter.mp hs).2,
    Finset.insert_erase (Finset.mem_filter.mp ht).2] using h

theorem mem_presentLayer_iff (F : Finset (Finset R)) (g : R) (S : Finset R) :
    S ∈ presentLayer F g ↔ g ∉ S ∧ insert g S ∈ F := by
  constructor
  · intro hs
    obtain ⟨W,hw,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨Finset.notMem_erase g W, by
      simpa only [Finset.insert_erase (Finset.mem_filter.mp hw).2] using
        (Finset.mem_filter.mp hw).1⟩
  · rintro ⟨hg,hs⟩
    exact Finset.mem_image.mpr ⟨insert g S,
      Finset.mem_filter.mpr ⟨hs,Finset.mem_insert_self g S⟩,
      Finset.erase_insert hg⟩

theorem presentLayer_card (F : Finset (Finset R)) (g : R) :
    (presentLayer F g).card = (F.filter fun S => g ∈ S).card := by
  exact Finset.card_image_iff.mpr (erase_injective_on_present F g)

theorem layer_card_identity (F : Finset (Finset R)) (g : R) :
    F.card = (absentLayer F g).card + (presentLayer F g).card := by
  rw [presentLayer_card]
  simpa only [absentLayer,not_not] using (Finset.card_filter_add_card_filter_not
    (s := F) (p := fun S => g ∉ S)).symm

theorem layer_frequency_identity (F : Finset (Finset R)) (g r : R) (hr : r ≠ g) :
    (F.filter (fun S => r ∈ S)).card =
      ((absentLayer F g).filter (fun S => r ∈ S)).card +
      ((presentLayer F g).filter (fun S => r ∈ S)).card := by
  have he : (presentLayer F g).filter (fun S => r ∈ S) =
      ((F.filter (fun S => g ∈ S)).filter (fun S => r ∈ S)).image
        (fun S => S.erase g) := by
    ext S
    simp only [Finset.mem_filter, presentLayer, Finset.mem_image]
    constructor
    · rintro ⟨⟨W,hw,rfl⟩,hrw⟩
      exact ⟨W,⟨hw,(Finset.mem_erase.mp hrw).2⟩,rfl⟩
    · rintro ⟨W,⟨hw,hrw⟩,rfl⟩
      exact ⟨⟨W,hw,rfl⟩,Finset.mem_erase.mpr ⟨hr,hrw⟩⟩
  rw [he, Finset.card_image_iff.mpr
    ((erase_injective_on_present F g).mono (Finset.filter_subset _ _))]
  have h := Finset.card_filter_add_card_filter_not
    (s := F.filter (fun S => r ∈ S)) (p := fun S => g ∉ S)
  simpa only [absentLayer,Finset.filter_filter,not_not,and_comm] using h.symm

/-- Integer bookkeeping for the defect bound. Its good-row average is an
explicit premise here; the literal structural proof is a separate obligation. -/
theorem defect_bound_of_good_average (F D : Finset (Finset R)) (U : Finset R)
    (hD : D ⊆ F)
    (hgood : U.card * (F \ D).card ≤ 2 * ∑ W ∈ F \ D, (W ∩ U).card) :
    U.card * (F.card - D.card) + 2 * ∑ W ∈ D, (W ∩ U).card ≤
      2 * ∑ W ∈ F, (W ∩ U).card := by
  have hc := Finset.card_sdiff_of_subset hD
  have hs := Finset.sum_sdiff hD (f := fun W => (W ∩ U).card)
  dsimp only at hs
  rw [hc] at hgood
  omega

end RAF.Frankl
