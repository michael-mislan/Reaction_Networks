import proofs.FutileCycle.PartitionedDeterminant

namespace FutileCycle

/-- The determinant theorem takes a literal child, not an assumed reduction. -/
theorem child_det_bound {S E C I : Type*} [DecidableEq S] [DecidableEq E]
    [DecidableEq C] [Fintype I] [DecidableEq I]
    (N : ConversionSystem S E C) (J : Child N I) :
    J.matrix.det = 0 ∨ J.matrix.det = 1 ∨ J.matrix.det = -1 := by
  classical
  let p : I → Prop := fun i => ∃ x : S ⊕ E, freeEmbed x = J.species i
  let U := {i // p i}
  let V := {i // ¬p i}
  have hu : ∀ i : U, ∃ x : S ⊕ E, freeEmbed x = J.species i.val := fun i => i.property
  choose f hfs using hu
  have hve : ∀ i : V, ∃ c : C, Sum.inr (Sum.inr c) = J.species i.val := by
    intro i
    rcases hsi : J.species i.val with s | e | c
    · exact False.elim (i.property ⟨.inl s, by simpa [freeEmbed] using hsi.symm⟩)
    · exact False.elim (i.property ⟨.inr e, by simpa [freeEmbed] using hsi.symm⟩)
    · exact ⟨c, rfl⟩
  choose v hvs using hve
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply J.species_injective
    rw [← hfs i, ← hfs j, hij]
  have hv : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    apply J.species_injective
    rw [← hvs i, ← hvs j, hij]
  let b : U → C := fun i => (J.reaction i.val).1
  have hb : ∀ i : U, (b i, Direction.bind) = J.reaction i.val := by
    intro i
    have hs := J.supported i.val
    rw [← hfs i] at hs
    have hd := free_owns_binding N (f i) (J.reaction i.val).1 (J.reaction i.val).2 hs
    exact Prod.ext rfl hd.symm
  have hvout : ∀ i : V, ∃ d : Bool, (v i, outgoing d) = J.reaction i.val := by
    intro i
    have hs := J.supported i.val
    rw [← hvs i] at hs
    obtain ⟨hc, hd⟩ := intermediate_owns_outgoing N (v i)
      (J.reaction i.val).1 (J.reaction i.val).2 hs
    rcases hd with hd | hd
    · exact ⟨false, Prod.ext hc (by simpa [outgoing] using hd.symm)⟩
    · exact ⟨true, Prod.ext hc (by simpa [outgoing] using hd.symm)⟩
  choose d hds using hvout
  let e : U ⊕ V ≃ I := Equiv.sumCompl p
  have hrow : ∀ i : U ⊕ V,
      Sum.elim (fun i => freeEmbed (f i)) (fun k => Sum.inr (Sum.inr (v k))) i =
        J.species (e i) := by
    intro i
    cases i with
    | inl i => exact hfs i
    | inr i => exact hvs i
  have hcol : ∀ i : U ⊕ V,
      Sum.elim (fun j => (b j, Direction.bind)) (fun k => (v k, outgoing (d k))) i =
        J.reaction (e i) := by
    intro i
    cases i with
    | inl i => exact hb i
    | inr i => exact hds i
  have heq : partitionedMatrix N f v b d = J.matrix.submatrix e e := by
    ext i j
    simp only [partitionedMatrix, hrow, hcol, Matrix.submatrix_apply, Child.matrix]
  have ht := partitioned_det_bound N f hf v hv b d
  rw [heq, Matrix.det_submatrix_equiv_self] at ht
  exact ht

theorem allN_child_det (n : ℕ) {I : Type*} [Fintype I] [DecidableEq I]
    (J : Child (futile n) I) :
    J.matrix.det = 0 ∨ J.matrix.det = 1 ∨ J.matrix.det = -1 :=
  child_det_bound (futile n) J

end FutileCycle
