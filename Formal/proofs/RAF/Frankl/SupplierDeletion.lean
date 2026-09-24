import proofs.RAF.Frankl.LocallyRankedSupplierCore

namespace RAF.Frankl
open RAF
variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

/-- RAF organizations surviving deletion, with all remaining incidences fixed. -/
noncomputable def survivingRAFs (Q : CRS M R) (C : Catalysis M R) (r : R) :=
  (rafFamily Q C).filter (fun W => r ∉ W)

theorem deletion_partition (Q : CRS M R) (C : Catalysis M R) (r : R) :
    (survivingRAFs Q C r).card + ((fixedFamily Q C).filter (fun W => r ∈ W)).card =
      (rafFamily Q C).card := by
  classical
  have hf : (fixedFamily Q C).filter (fun W => r ∈ W) =
      (rafFamily Q C).filter (fun W => r ∈ W) := by
    ext W
    simp only [Finset.mem_filter,mem_fixedFamily,mem_rafFamily]
    constructor
    · rintro ⟨he|hh,hr⟩
      · subst W; simp at hr
      · exact ⟨hh,hr⟩
    · exact fun hh => ⟨Or.inr hh.1,hh.2⟩
  rw [hf]
  have h := Finset.card_filter_add_card_filter_not (s := rafFamily Q C) (p := fun W => r ∈ W)
  simpa only [survivingRAFs,Nat.add_comm] using h

theorem local_supplier_deletion (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (rank : R → ℕ) (hrank : InternalSubstrateRank Q U rank)
    (hU : SupplierCore Q C U) :
    ∃ r ∈ U, 2*(survivingRAFs Q C r).card + 1 ≤ (rafFamily Q C).card := by
  classical
  obtain ⟨r,hr,hf⟩ := local_supplier_core_exists_abundant Q C U rank hrank hU
  refine ⟨r,hr,?_⟩
  have he : (∅ : Finset R) ∉ rafFamily Q C := by
    rw [mem_rafFamily]
    intro h
    simpa using h.1
  have hc : (fixedFamily Q C).card = (rafFamily Q C).card+1 := by simp [fixedFamily,he]
  have hp := deletion_partition Q C r
  rw [hc] at hf
  omega

end RAF.Frankl
