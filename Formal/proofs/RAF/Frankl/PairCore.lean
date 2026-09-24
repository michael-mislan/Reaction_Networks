import proofs.RAF.Frankl.PairAvailability

namespace RAF.Frankl.PairGadget
open RAF RAFQueryCompilation PairReaction PairMolecule
open scoped Classical
variable {U : Type*} [Fintype U] [DecidableEq U]

theorem no_blockers_iff_singleton (D : UnionClosedData U) (i : U) :
    (∀ B, ¬ D.IsBlocker i B) ↔ {i} ∈ D.family := by
  constructor
  · intro h
    have hm : i ∈ D.interior {i} :=
      (D.mem_interior_iff_hits_blockers (Finset.mem_singleton_self i)).mpr
        (fun B hB => (h B hB).elim)
    have he : D.interior {i} = {i} := Finset.Subset.antisymm
      (D.interior_subset _) (Finset.singleton_subset_iff.mpr hm)
    exact (D.fixed_iff_mem _).mp he
  · intro hs B hB
    exact hB.2 ((D.mem_interior _ i).mpr
      ⟨{i}, hs, by simpa using hB.1, Finset.mem_singleton_self i⟩)

theorem gate_food_ready_iff_singleton (D : UnionClosedData U) (i : U) :
    SeedReaction (crs D) (gate i) ↔ {i} ∈ D.family := by
  rw [← no_blockers_iff_singleton]
  constructor
  · intro h B hB
    have hm : marker i B ∈ (crs D).inputs (gate i) := by simp [crs, hB]
    have := h hm
    simp [crs] at this
  · intro h x hx
    cases x with
    | food => simp [crs]
    | alpha j => simp [crs] at hx
    | beta j => simp [crs] at hx
    | marker j B =>
        have hj : j = i ∧ D.IsBlocker i B := by simpa [crs] using hx
        exact (h B hj.2).elim

noncomputable def singletonCoordinates (D : UnionClosedData U) : Finset U :=
  Finset.univ.filter fun i => {i} ∈ D.family

theorem singletonCoordinates_fixed (D : UnionClosedData U) :
    D.interior (singletonCoordinates D) = singletonCoordinates D := by
  apply Finset.Subset.antisymm (D.interior_subset _)
  intro i hi
  exact (D.mem_interior _ i).mpr ⟨{i}, (Finset.mem_filter.mp hi).2,
    Finset.singleton_subset_iff.mpr hi, Finset.mem_singleton_self i⟩

/-- Exact elementary maxRAF of the sparse universal source. -/
theorem evaluate_food_ready_eq_singletons (D : UnionClosedData U) :
    evaluate (crs D) catalysis (Finset.univ.filter (SeedReaction (crs D))) =
      encode (singletonCoordinates D) := by
  rw [evaluate_eq_encode_interior]
  have hp : completePairs (Finset.univ.filter (SeedReaction (crs D))) =
      singletonCoordinates D := by
    ext i
    have hprod : SeedReaction (crs D) (producer i) := by
      intro x hx
      simpa [crs] using hx
    simp [singletonCoordinates, hprod, gate_food_ready_iff_singleton]
  rw [hp, singletonCoordinates_fixed]

end RAF.Frankl.PairGadget
