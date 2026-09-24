import proofs.ProductiveMemory.ExtractionMaterialService

namespace ProductiveMemory
open FiniteCopy HeritableCompositions
open scoped NNReal
noncomputable section
set_option Elab.async false

/-- Recovery's physical extraction tally. Rates and chemistry are unchanged. -/
def extractionMarkIndex (J : ℕ) (c : Fin (J+1)) (r : ExtractionChannel) : Fin (J+1) :=
  ⟨min (c.val+collectionMark r) J,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def extractionMarkModel {α : Type*} [Fintype α]
    (M : FiniteJumpModel α ExtractionChannel) (J : ℕ) : FiniteJumpModel (α × Fin (J+1)) ExtractionChannel where
  next s r := (M.next s.1 r,extractionMarkIndex J s.2 r)
  rate s r := M.rate s.1 r
  nonneg s r := M.nonneg s.1 r

variable {α : Type*} [Fintype α] [DecidableEq α]
  (M : FiniteJumpModel α ExtractionChannel) (J : ℕ)

theorem extraction_mark_step_projection (q : ℝ) (hq : 0 < q) (hb : ∀ x, M.total x ≤ q)
    (f : α → ℝ) (s : α × Fin (J+1)) :
    ((extractionMarkModel M J).uniformize q hq (fun z => hb z.1)).step
      (fun z => f z.1) s = (M.uniformize q hq hb).step f s.1 := by
  rw [FiniteJumpModel.uniformize_step, FiniteJumpModel.uniformize_step]
  rfl

theorem extraction_mark_steps_projection (q : ℝ) (hq : 0 < q) (hb : ∀ x, M.total x ≤ q)
    (n : ℕ) (f : α → ℝ) (s : α × Fin (J+1)) :
    ((extractionMarkModel M J).uniformize q hq (fun z => hb z.1)).steps n
      (fun z => f z.1) s = (M.uniformize q hq hb).steps n f s.1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change ((extractionMarkModel M J).uniformize q hq (fun z => hb z.1)).step
      (((extractionMarkModel M J).uniformize q hq (fun z => hb z.1)).steps n
        (fun z => f z.1)) s = _
    rw [show ((extractionMarkModel M J).uniformize q hq (fun z => hb z.1)).steps n
        (fun z => f z.1) = (fun z => (M.uniformize q hq hb).steps n f z.1)
      from funext ih]
    exact extraction_mark_step_projection M J q hq hb _ s

theorem extraction_mark_poissonized_projection (q : ℝ) (hq : 0 < q)
    (hb : ∀ x, M.total x ≤ q) (t : ℝ≥0) (f : α → ℝ) (s : α × Fin (J+1)) :
    ((extractionMarkModel M J).uniformize q hq (fun z => hb z.1)).poissonized t
      (fun z => f z.1) s = (M.uniformize q hq hb).poissonized t f s.1 := by
  unfold FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [extraction_mark_steps_projection]


omit [DecidableEq α] in
theorem extraction_mark_run_count (s : α × Fin (J+1)) (rs : List ExtractionChannel) :
    (SerialTransferSelection.eventRun (extractionMarkModel M J) s rs).2.val =
      min (s.2.val+(rs.map collectionMark).sum) J := by
  induction rs generalizing s with
  | nil => simp [SerialTransferSelection.eventRun,Nat.min_eq_left (Nat.le_of_lt_succ s.2.isLt)]
  | cons r rs ih =>
    rw [SerialTransferSelection.eventRun,ih]
    simp only [extractionMarkModel,extractionMarkIndex,List.map_cons,List.sum_cons]
    have hc := s.2.isLt
    omega

omit [DecidableEq α] in
theorem extraction_mark_unsaturated_exact (s : α) (rs : List ExtractionChannel)
    (hs : (SerialTransferSelection.eventRun (SerialTransferSelection.serviceCounterModel M J) (s,0) rs).2.val < J) :
    (SerialTransferSelection.eventRun (extractionMarkModel M J) (s,0) rs).2.val=(rs.map collectionMark).sum := by
  rw [extraction_mark_run_count]
  simp only [Fin.val_zero,zero_add]
  apply Nat.min_eq_left
  have hb := SerialTransferSelection.service_run_material_budget M J s rs collectionMark
    (by intro r; cases r <;> simp [collectionMark]) hs
  exact hb.le

end
end ProductiveMemory
