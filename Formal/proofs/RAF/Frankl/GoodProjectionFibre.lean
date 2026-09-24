import proofs.RAF.Frankl.CoreAbundance

namespace RAF.Frankl

open RAF
open scoped Classical

variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

/-- The fibre with valid isolated-core projection, retaining its exterior context. -/
noncomputable def goodProjectionFibre (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) : Finset (Finset {r // r ∈ U}) :=
  Finset.univ.powerset.filter fun S =>
    fromRestricted S ∪ T ∈ fixedFamily Q C ∧ fromRestricted S ∈ fixedFamily Q C

theorem good_projection_fibre_iff (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (S : Finset {r // r ∈ U}) :
    (fromRestricted S ∪ T ∈ fixedFamily Q C ∧ fromRestricted S ∈ fixedFamily Q C) ↔
      exteriorGood Q C U T S ∧ fromRestricted S ∈ fixedFamily Q C := by
  constructor
  · rintro ⟨hw,hs⟩
    have h := (fixedFamily_iff_food_support Q C _).mp hw
    exact ⟨⟨h.1,fun r hr => h.2 r (Finset.mem_union_right _ hr)⟩,hs⟩
  · rintro ⟨⟨hf,ht⟩,hs⟩
    refine ⟨(fixedFamily_iff_food_support Q C _).mpr ⟨hf,?_⟩,hs⟩
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact extensionSupport_mono Q C Finset.subset_union_left
        ((fixedFamily_iff_food_support Q C _).mp hs |>.2 r hr)
    · exact ht r hr

theorem elementary_restriction_fixed_iff (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (hE : ∀ r ∈ U, SeedReaction Q r)
    (S : Finset {r // r ∈ U}) :
    fromRestricted S ∈ fixedFamily Q C ↔
      ¬ dependencyHornDNF (extensionBody Q C U ∅) (Finset.univ \ S) := by
  have hg : exteriorGood Q C U ∅ S := by
    constructor
    · intro r hr
      have hr' : r ∈ fromRestricted S := by simpa using hr
      exact ⟨0,hE r ((mem_fromRestricted S r).mp hr').1⟩
    · simp
  have h := extension_fibre_iff Q C U ∅ S
  simpa only [Finset.union_empty,hg,true_and] using h

/-- Good projections retain half occupancy in each exterior context, measured
on the original viable elementary core, even when other projections are bad. -/
theorem goodProjectionFibre_average (Q : CRS M R) (C : Catalysis M R)
    (U T : Finset R) (hU : IsRAF Q C U) (hE : ∀ r ∈ U, SeedReaction Q r) :
    (goodProjectionFibre Q C U T).card * Fintype.card {r // r ∈ U} ≤
      2 * ∑ S ∈ goodProjectionFibre Q C U T, S.card := by
  classical
  let d : {r // r ∈ U} → {r // r ∈ U} := fun r =>
    Classical.choose (extensionBody_nonempty Q C U ∅ hU r)
  have hd : ∀ r, d r ∈ extensionBody Q C U ∅ r := fun r =>
    Classical.choose_spec (extensionBody_nonempty Q C U ∅ hU r)
  have h := supported_upward_average (extensionBody Q C U ∅) d hd
    (exteriorGood Q C U T) (fun hab => exteriorGood_mono Q C U T hE hab)
  have heq : goodProjectionFibre Q C U T = Finset.univ.powerset.filter
      (fun S => exteriorGood Q C U T S ∧
        ¬ dependencyHornDNF (extensionBody Q C U ∅) (Finset.univ \ S)) := by
    ext S
    simp only [goodProjectionFibre,Finset.mem_filter]
    rw [good_projection_fibre_iff,
      elementary_restriction_fixed_iff Q C U hE]
  rw [heq]
  exact h

end RAF.Frankl
