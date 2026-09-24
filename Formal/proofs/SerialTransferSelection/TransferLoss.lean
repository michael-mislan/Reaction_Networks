import proofs.SerialTransferSelection.TransferLaw

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

theorem uniformFiniteLaw_event_card {α : Type*} [Fintype α] [Nonempty α]
    (A : Set α) [DecidablePred (· ∈ A)] : (uniformFiniteLaw α).expect (FiniteKernel.eventIndicator A) =
      (Fintype.card {x // x ∈ A} : ℝ)/(Fintype.card α : ℝ) := by
  classical
  simp only [FiniteLaw.expect,uniformFiniteLaw,FiniteKernel.eventIndicator,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simp [Fintype.card_subtype,div_eq_mul_inv]

theorem transferSubset_card (n m : ℕ) : Fintype.card (TransferSubset n m) = n.choose m := by
  classical
  let e : TransferSubset n m ≃ {S // S ∈ (Finset.univ : Finset (Fin n)).powersetCard m} := {
    toFun := fun S => ⟨S.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,S.property⟩⟩
    invFun := fun S => ⟨S.val,(Finset.mem_powersetCard.mp S.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard]
  simp

/-- Exact loss under the literal uniform subset law, including empty/full edge cases. -/
theorem uniformTransfer_loss (n m : ℕ) (hm : m ≤ n) (A : Finset (Fin n)) :
    (uniformTransferLaw n m hm).expect
      (FiniteKernel.eventIndicator {S | Disjoint S.val A}) =
      ((n-A.card).choose m : ℝ)/(n.choose m : ℝ) := by
  classical
  letI := transfer_subset_nonempty n m hm
  change (uniformFiniteLaw (TransferSubset n m)).expect _ = _
  rw [uniformFiniteLaw_event_card,transferSubset_card]
  let e : {S : TransferSubset n m // Disjoint S.val A} ≃
      {S // S ∈ ((Finset.univ : Finset (Fin n)) \ A).powersetCard m} := {
    toFun := fun S => ⟨S.val.val,Finset.mem_powersetCard.mpr ⟨by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun ha =>
        Finset.disjoint_left.mp S.property hi ha⟩,S.val.property⟩⟩
    invFun := fun S => ⟨⟨S.val,(Finset.mem_powersetCard.mp S.property).2⟩,by
      apply Finset.disjoint_left.mpr
      intro i hi ha
      exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp S.property).1 hi)).2 ha⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe,Finset.card_powersetCard,Finset.card_sdiff_of_subset (Finset.subset_univ A)] at hc
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  have hc' : Fintype.card {x : TransferSubset n m // x ∈ {S | Disjoint S.val A}} =
      (n-A.card).choose m := (Fintype.card_congr (Equiv.refl _)).trans hc
  exact congrArg (fun k : ℕ => (k : ℝ)/(n.choose m : ℝ)) hc'

end SerialTransferSelection
