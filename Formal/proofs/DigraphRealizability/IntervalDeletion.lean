import proofs.DigraphRealizability.ComplementBridge

namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

def deleteInterval (U : Finset (Finset E)) (S : Finset E) (r : E) :
    Finset (Finset E) :=
  U.filter fun X => ¬ (r ∈ X ∧ X ⊆ S)

/-- Direct set-family procedure. Its inputs contain no graph or Horn presentation. -/
inductive Peels (F : Finset (Finset E)) : Finset (Finset E) → Set E → Prop
  | done (H) : Peels F F H
  | step {U H S r}
      (bad : S ∈ U ∧ S ∉ F)
      (maximal : ∀ T ∈ U, T ∉ F → S ⊆ T → T = S)
      (inside : r ∈ S)
      (absent : ∀ T ∈ F, T ⊆ S → r ∉ T)
      (fresh : r ∉ H)
      (tail : Peels F (deleteInterval U S r) (insert r H)) :
      Peels F U H

def IntrinsicPeelable (F : Finset (Finset E)) : Prop := Peels F Finset.univ ∅

theorem dual_trim (U : Finset (Finset E)) (B : Finset E) (r : E) :
    dual (trim U B r) = deleteInterval (dual U) Bᶜ r := by
  classical
  ext X
  simp only [mem_dual, trim, deleteInterval, Finset.mem_filter, Finset.mem_compl]
  rw [Finset.subset_compl_comm]
  tauto

theorem dual_delete (U : Finset (Finset E)) (S : Finset E) (r : E) :
    dual (deleteInterval U S r) = trim (dual U) Sᶜ r := by
  have h := congrArg dual (dual_trim (dual U) Sᶜ r)
  simpa using h.symm

@[simp] theorem dual_univ : dual (Finset.univ : Finset (Finset E)) = Finset.univ := by
  ext X
  simp

theorem Eliminates.toPeels {K U : Finset (Finset E)} {H : Set E}
    (run : Eliminates K U H) : Peels (dual K) (dual U) H := by
  classical
  induction run with
  | done H => exact Peels.done H
  | @step U H B r bad minimal outside forced fresh _ ih =>
    rw [dual_trim] at ih
    refine Peels.step ?_ ?_ (Finset.mem_compl.mpr outside) ?_ fresh ih
    · simpa using bad
    · intro T hTU hTK hBT
      have hsub : Tᶜ ⊆ B := by
        simpa using (Finset.compl_subset_compl.mpr hBT)
      have eq := minimal Tᶜ ((mem_dual U T).mp hTU)
        (fun h => hTK ((mem_dual K T).mpr h)) hsub
      simpa using congrArg (fun X : Finset E => Xᶜ) eq
    · intro T hTK hTB
      have hb : B ⊆ Tᶜ := Finset.subset_compl_comm.mp hTB
      exact Finset.mem_compl.mp (forced Tᶜ ((mem_dual K T).mp hTK) hb)

theorem Peels.toEliminates {F U : Finset (Finset E)} {H : Set E}
    (run : Peels F U H) : Eliminates (dual F) (dual U) H := by
  classical
  induction run with
  | done H => exact Eliminates.done H
  | @step U H S r bad maximal inside absent fresh _ ih =>
    rw [dual_delete] at ih
    refine Eliminates.step ?_ ?_ ?_ ?_ fresh ih
    · simpa using bad
    · intro T hTU hTF hTS
      have hsub : S ⊆ Tᶜ := Finset.subset_compl_comm.mp hTS
      have eq := maximal Tᶜ ((mem_dual U T).mp hTU)
        (fun h => hTF ((mem_dual F T).mpr h)) hsub
      simpa using congrArg (fun X : Finset E => Xᶜ) eq
    · simpa using inside
    · intro X hXF hSX
      have hsub : Xᶜ ⊆ S := by
        simpa using (Finset.compl_subset_compl.mpr hSX)
      have h := absent Xᶜ ((mem_dual F X).mp hXF) hsub
      simpa using h

theorem intrinsic_iff_complement (F : Finset (Finset E)) :
    IntrinsicPeelable F ↔ ComplementPeelable F := by
  constructor
  · intro h
    have h' := Peels.toEliminates h
    simpa [ComplementPeelable] using h'
  · intro h
    have h' := Eliminates.toPeels h
    simpa [IntrinsicPeelable] using h'

/-- Exact same-ground characterization, including loops and absent coordinates.
No closure or successful-completion hypothesis is assumed. -/
theorem digraphRealizable_iff_intrinsicPeeling (F : Finset (Finset E)) :
    (∃ P : E → Finset E, ∀ S, S ∈ F ↔ RAFInteriorRealizability.PredSupported P S) ↔
      IntrinsicPeelable F :=
  (digraphRealizable_iff_complementPeelable F).trans (intrinsic_iff_complement F).symm

omit [Fintype E] in
theorem eligible_iff_interior (F : RAF.Frankl.UnionClosedData E) (S : Finset E) (r : E) :
    (∀ T ∈ F.family, T ⊆ S → r ∉ T) ↔ r ∉ F.interior S := by
  rw [RAF.Frankl.UnionClosedData.mem_interior]
  push Not
  rfl

theorem interiorOperator_iff_intrinsicPeeling (F : RAFInteriorRealizability.InteriorOperator E) :
    (∃ P : E → Finset E, ∀ S,
      F.apply S = S ↔ RAFInteriorRealizability.PredSupported P S) ↔
      IntrinsicPeelable F.family := by
  simp only [RAFInteriorRealizability.InteriorOperator.fixed_iff_mem]
  exact digraphRealizable_iff_intrinsicPeeling F.family
end DigraphRealizability
