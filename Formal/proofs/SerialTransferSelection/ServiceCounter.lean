import proofs.FiniteCopy.UniformizedBounds

namespace SerialTransferSelection
open FiniteCopy
open scoped NNReal

def serviceIndex (J : ℕ) (c : Fin (J+1)) : Fin (J+1) :=
  ⟨min (c.val+1) J, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- The counter saturates, but the physical source continues unchanged. -/
noncomputable def serviceCounterModel {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (J : ℕ) : FiniteJumpModel (α × Fin (J+1)) β where
  next s r := (M.next s.1 r, serviceIndex J s.2)
  rate s r := M.rate s.1 r
  nonneg s r := M.nonneg s.1 r

variable {α β : Type*} [Fintype α] [Fintype β]
  (M : FiniteJumpModel α β) (J : ℕ)

theorem service_total (s : α × Fin (J+1)) :
    (serviceCounterModel M J).total s = M.total s.1 := rfl

theorem service_generator_projection (f : α → ℝ) (s : α × Fin (J+1)) :
    (serviceCounterModel M J).generator (fun z => f z.1) s =
      M.generator f s.1 := rfl

theorem service_counter_drift (s : α × Fin (J+1)) :
    (serviceCounterModel M J).generator (fun z => (z.2.val : ℝ)) s ≤ M.total s.1 := by
  have hi : ((serviceIndex J s.2).val : ℝ) - s.2.val ≤ 1 := by
    have hn : (serviceIndex J s.2).val ≤ s.2.val+1 := Nat.min_le_left _ _
    have hr : ((serviceIndex J s.2).val : ℝ) ≤ (s.2.val : ℝ)+1 := by exact_mod_cast hn
    linarith
  apply Finset.sum_le_sum
  intro r _
  exact (mul_le_mul_of_nonneg_left hi (M.nonneg s.1 r)).trans_eq (mul_one _)

variable [DecidableEq α]

theorem service_step_projection (q : ℝ) (hq : 0 < q) (hb : ∀ x, M.total x ≤ q)
    (f : α → ℝ) (s : α × Fin (J+1)) :
    ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).step
      (fun z => f z.1) s = (M.uniformize q hq hb).step f s.1 := by
  rw [FiniteJumpModel.uniformize_step, FiniteJumpModel.uniformize_step]
  rfl

theorem service_steps_projection (q : ℝ) (hq : 0 < q) (hb : ∀ x, M.total x ≤ q)
    (n : ℕ) (f : α → ℝ) (s : α × Fin (J+1)) :
    ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).steps n
      (fun z => f z.1) s = (M.uniformize q hq hb).steps n f s.1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).step
      (((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).steps n
        (fun z => f z.1)) s = _
    rw [show ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).steps n
        (fun z => f z.1) = (fun z => (M.uniformize q hq hb).steps n f z.1)
      from funext ih]
    exact service_step_projection M J q hq hb _ s

theorem service_poissonized_projection (q : ℝ) (hq : 0 < q)
    (hb : ∀ x, M.total x ≤ q) (t : ℝ≥0) (f : α → ℝ) (s : α × Fin (J+1)) :
    ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).poissonized t
      (fun z => f z.1) s = (M.uniformize q hq hb).poissonized t f s.1 := by
  unfold FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [service_steps_projection]

theorem service_quota_scaled_bound (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hb : ∀ x, M.total x ≤ q) (x : α) :
    (J : ℝ) * ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).poissonized
      (q*t) (FiniteKernel.eventIndicator {s | s.2.val = J}) (x, 0) ≤ (t : ℝ)*q := by
  have h := (serviceCounterModel M J).uniformized_event_bound q t hq
    (fun z => hb z.1) {s | s.2.val = J} (fun z => (z.2.val : ℝ)) J q
    (fun _ => Nat.cast_nonneg _) (fun s hs => by simp only [Set.mem_setOf_eq] at hs; simp [hs])
    (fun s => (service_counter_drift M J s).trans (hb s.1)) (x, 0)
  simpa using h

end SerialTransferSelection
