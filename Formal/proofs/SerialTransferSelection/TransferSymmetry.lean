import proofs.SerialTransferSelection.TransferLaw

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

theorem uniformFiniteLaw_expect_equiv {α : Type*} [Fintype α] [Nonempty α]
    (e : α ≃ α) (f : α → ℝ) :
    (uniformFiniteLaw α).expect (fun x => f (e x))=(uniformFiniteLaw α).expect f := by
  exact e.sum_comp (fun x => (Fintype.card α : ℝ)⁻¹*f x)

noncomputable def transferSubsetEquiv (L M : ℕ) (e : Fin L ≃ Fin L) :
    TransferSubset L M ≃ TransferSubset L M where
  toFun S := ⟨S.val.map e.toEmbedding, by simp [S.property]⟩
  invFun S := ⟨S.val.map e.symm.toEmbedding, by simp [S.property]⟩
  left_inv S := by apply Subtype.ext; ext i; simp
  right_inv S := by apply Subtype.ext; ext i; simp

theorem uniformTransferLaw_equiv (L M : ℕ) (hM : M ≤ L) (e : Fin L ≃ Fin L)
    (f : TransferSubset L M → ℝ) :
    (uniformTransferLaw L M hM).expect (fun S => f (transferSubsetEquiv L M e S))=
      (uniformTransferLaw L M hM).expect f := by
  classical
  letI := transfer_subset_nonempty L M hM
  exact uniformFiniteLaw_expect_equiv (transferSubsetEquiv L M e) f

noncomputable def subsetIndicator {L M : ℕ} (i : Fin L) (S : TransferSubset L M) : ℝ :=
  if i ∈ S.val then 1 else 0

theorem subsetIndicator_equiv (L M : ℕ) (e : Fin L ≃ Fin L) (i : Fin L)
    (S : TransferSubset L M) :
    subsetIndicator (e i) (transferSubsetEquiv L M e S)=subsetIndicator i S := by
  simp [subsetIndicator,transferSubsetEquiv]

theorem subset_marginals_equal (L M : ℕ) (hM : M ≤ L) (i j : Fin L) :
    (uniformTransferLaw L M hM).expect (subsetIndicator i)=
      (uniformTransferLaw L M hM).expect (subsetIndicator j) := by
  have h := uniformTransferLaw_equiv L M hM (Equiv.swap i j) (subsetIndicator j)
  simpa [subsetIndicator,transferSubsetEquiv] using h

theorem subset_pair_swap (L M : ℕ) (hM : M ≤ L) (i j k : Fin L)
    (hij : i ≠ j) (hik : i ≠ k) :
    (uniformTransferLaw L M hM).expect (fun S => subsetIndicator i S*subsetIndicator j S)=
      (uniformTransferLaw L M hM).expect (fun S => subsetIndicator i S*subsetIndicator k S) := by
  have h := uniformTransferLaw_equiv L M hM (Equiv.swap j k)
    (fun S => subsetIndicator i S*subsetIndicator k S)
  simpa [subsetIndicator,transferSubsetEquiv,Equiv.swap_apply_of_ne_of_ne hij hik] using h

end SerialTransferSelection
