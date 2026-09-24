import proofs.IrrRAFEnumeration.PositiveEnumeration

namespace IrrRAFEnumeration
open RAF

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Restrict reaction identifiers only, retaining food and incidence data. -/
def restrictCRS (Q : CRS M R) (U : Finset R) : CRS M {r // r ∈ U} where
  food := Q.food
  inputs r := Q.inputs r.val
  outputs r := Q.outputs r.val

theorem restrict_closureAt (Q : CRS M R) (U : Finset R)
    (S : Finset {r // r ∈ U}) (t : Nat) :
    closureAt (restrictCRS Q U) S t = closureAt Q (S.image Subtype.val) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [closureAt, closureStep, ih, Finset.image_biUnion]
    rfl

theorem restrict_isRAF (Q : CRS M R) (C : Catalysis M R) (U : Finset R)
    (S : Finset {r // r ∈ U}) :
    IsRAF (restrictCRS Q U) (fun x r => C x r.val) S ↔
      IsRAF Q C (S.image Subtype.val) := by
  simp only [IsRAF, FoodGenerated, ReflexivelyAutocatalytic,
    CatalyzedFromClosure, restrict_closureAt, Finset.forall_mem_image,
    Finset.image_nonempty]
  rfl

omit [DecidableEq R] in
/-- Minimality commutes with imposing an allowed reaction container. -/
theorem minimal_within_iff {P : Finset R → Prop} {U I : Finset R} :
    Minimal (fun S => S ⊆ U ∧ P S) I ↔ Minimal P I ∧ I ⊆ U := by
  constructor
  · rintro ⟨⟨hIU,hI⟩,hm⟩
    refine ⟨⟨hI,?_⟩,hIU⟩
    intro J hJ hJI
    exact hm ⟨hJI.trans hIU,hJ⟩ hJI
  · rintro ⟨⟨hI,hm⟩,hIU⟩
    exact ⟨⟨hIU,hI⟩,fun _ hJ hJI => hm hJ.2 hJI⟩

variable [Fintype R]

/-- Restricted families expressed with the original explicit identifiers. -/
noncomputable def familyWithin (Q : CRS M R) (C : Catalysis M R) (U : Finset R) :=
  (irrRAFFamily Q C).filter (fun I => I ⊆ U)

theorem mem_familyWithin (Q : CRS M R) (C : Catalysis M R) (U I : Finset R) :
    I ∈ familyWithin Q C U ↔ Minimal (fun S => S ⊆ U ∧ IsRAF Q C S) I := by
  classical
  rw [minimal_within_iff]
  change I ∈ (irrRAFFamily Q C).filter (fun J => J ⊆ U) ↔ _
  rw [Finset.mem_filter, mem_irrRAFFamily]
  rfl

/-- The filtered exactness oracle is exactly the positive RAF witness oracle.
In particular it cannot invent an extra member when known sets leave U. -/
theorem filtered_completion_iff_available (Q : CRS M R) (C : Catalysis M R)
    (G : Finset (Finset R)) (hG : G ⊆ irrRAFFamily Q C) (U : Finset R) :
    familyWithin Q C U ≠ G.filter (fun I => I ⊆ U) ↔
      PositiveCompletion.Available (IsRAF Q C) G U := by
  classical
  have hsub : G.filter (fun I => I ⊆ U) ⊆ familyWithin Q C U := by
    intro I hI
    obtain ⟨hIG,hIU⟩ := Finset.mem_filter.mp hI
    exact Finset.mem_filter.mpr ⟨hG hIG,hIU⟩
  constructor
  · intro hne
    have hex : ∃ I ∈ familyWithin Q C U, I ∉ G.filter (fun I => I ⊆ U) := by
      by_contra hn
      apply hne
      apply Finset.Subset.antisymm _ hsub
      intro I hI
      by_contra hi
      exact hn ⟨I,hI,hi⟩
    obtain ⟨I,hI,hnew⟩ := hex
    obtain ⟨hIF,hIU⟩ := Finset.mem_filter.mp hI
    have hm := (mem_irrRAFFamily Q C I).mp hIF
    refine ⟨I,hIU,hm.1,?_⟩
    intro J hJG hJI
    have hIJ := hm.2 J ((mem_irrRAFFamily Q C J).mp (hG hJG)).1 hJI
    have he : I = J := Finset.Subset.antisymm hIJ hJI
    exact hnew (Finset.mem_filter.mpr ⟨he.symm ▸ hJG,hIU⟩)
  · rintro ⟨S,hSU,hS,havoid⟩ he
    obtain ⟨I,hIS,hI⟩ := exists_minimal_subset (IsRAF Q C) hS
    have hi : I ∈ familyWithin Q C U :=
      Finset.mem_filter.mpr ⟨(mem_irrRAFFamily Q C I).mpr hI,hIS.trans hSU⟩
    rw [he] at hi
    exact havoid I (Finset.mem_filter.mp hi).1 hIS

end IrrRAFEnumeration
