import proofs.RAFInteriorRealizability.AntimatroidRealization

namespace RAFInteriorRealizability

open RAF RAF.Frankl MarkerMolecule

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

namespace MarkerSource

/-- The private catalyst produced by reaction `u` realizes precisely the
chosen predecessor edge `u ∈ P e`. -/
theorem productGraphCatalyzed_iff_predSupported
    (A : AntimatroidData E) (P : E → Finset E) (S : Finset E) :
    ProductGraphCatalyzed (crs A) (catalysis P) S ↔ PredSupported P S := by
  constructor
  · intro h e he
    rcases h e he with hfood | ⟨u, huS, x, hxout, hxcat⟩
    · rcases hfood with ⟨x, hxfood, hxcat⟩
      have hx : x = food := by simpa [crs] using hxfood
      subst x
      simp [catalysis] at hxcat
    · refine ⟨u, huS, ?_⟩
      cases x with
      | food => simp [catalysis] at hxcat
      | catalyst v =>
          have hvu : v = u := by simpa [crs] using hxout
          subst v
          simpa [catalysis] using hxcat
      | marker target B => simp [catalysis] at hxcat
  · intro h e he
    obtain ⟨u, huS, huP⟩ := h e he
    exact Or.inr ⟨u, huS, catalyst u, by simp [crs], by simpa [catalysis]⟩

/-- The nonempty RAFs of the marker construction are exactly the nonempty
sets lying in the antimatroid shell and satisfying predecessor support. -/
theorem isRAF_iff_mem_and_predSupported
    (A : AntimatroidData E) (P : E → Finset E) (S : Finset E) :
    IsRAF (crs A) (catalysis P) S ↔
      S.Nonempty ∧ S ∈ A.family ∧ PredSupported P S := by
  rw [RAF.Frankl.isRAF_iff_foodGenerated_and_productGraph,
    foodGenerated_iff_mem, productGraphCatalyzed_iff_predSupported]

/-- Package the marker construction as a literal same-ground realization. -/
noncomputable def realization (A : AntimatroidData E)
    (P : E → Finset E) : LiteralRealization E := {
  M := MarkerMolecule E
  fintypeM := inferInstance
  decEqM := inferInstance
  Q := crs A
  C := catalysis P
}

theorem mem_realization_fixedData_iff
    (A : AntimatroidData E) (P : E → Finset E) (S : Finset E) :
    S ∈ (realization A P).fixedData.family ↔
      S ∈ A.family ∧ PredSupported P S := by
  rw [show (realization A P).fixedData.family =
      fixedFamily (crs A) (catalysis P) by rfl]
  rw [mem_fixedFamily]
  constructor
  · intro h
    rcases h with hzero | hraf
    · subst S
      exact ⟨A.empty_mem, by simp [PredSupported]⟩
    · exact (isRAF_iff_mem_and_predSupported A P S).1 hraf |>.2
  · intro hAP
    by_cases hzero : S = ∅
    · exact Or.inl hzero
    · exact Or.inr <| (isRAF_iff_mem_and_predSupported A P S).2
        ⟨Finset.nonempty_iff_ne_empty.mpr hzero, hAP⟩

end MarkerSource

end RAFInteriorRealizability
