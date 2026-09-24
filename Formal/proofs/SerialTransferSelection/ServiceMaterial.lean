import proofs.SerialTransferSelection.ServiceCounter
import proofs.CommonPhysicalRealization.ResidentCompletion

namespace SerialTransferSelection
open FiniteCopy

/-- Reservoir order F,G,RA,RB,WH. Counts both supply and collection, never netting
opposite exchanges. The last directed source channel collects H as WH. -/
def residentGrossExchange (r : Fin 13) (k : Fin 5) : ℕ :=
  if h : r.val < 12 then
    CommonPhysicalRealization.Resident.left ⟨r.val/2, by omega⟩ ⟨k.val+4, by omega⟩ +
    CommonPhysicalRealization.Resident.right ⟨r.val/2, by omega⟩ ⟨k.val+4, by omega⟩
  else if k.val=4 then 1 else 0

theorem resident_gross_exchange_le_one (r : Fin 13) (k : Fin 5) :
    residentGrossExchange r k ≤ 1 := by
  revert r k
  decide

def eventRun {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (s : α) : List β → α
  | [] => s
  | r :: rs => eventRun M (M.next s r) rs

theorem service_run_projection {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (J : ℕ) (s : α × Fin (J+1)) (rs : List β) :
    (eventRun (serviceCounterModel M J) s rs).1 = eventRun M s.1 rs := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem service_run_counter {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (J : ℕ) (s : α × Fin (J+1)) (rs : List β) :
    (eventRun (serviceCounterModel M J) s rs).2.val = min (s.2.val+rs.length) J := by
  induction rs generalizing s with
  | nil => simp [eventRun, Nat.min_eq_left (Nat.le_of_lt_succ s.2.isLt)]
  | cons r rs ih =>
    rw [eventRun, ih]
    simp only [serviceCounterModel, serviceIndex, List.length_cons]
    have hc := s.2.isLt
    omega

theorem event_gross_bound {β : Type*} (cost : β → ℕ) (hcost : ∀ r, cost r ≤ 1)
    (rs : List β) : (rs.map cost).sum ≤ rs.length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hr := hcost r
    omega

/-- Any actual event word with an unsaturated counter respects every service
whose literal per-event gross exchange is at most one. -/
theorem service_run_material_budget {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (J : ℕ) (x : α) (rs : List β)
    (cost : β → ℕ) (hcost : ∀ r, cost r ≤ 1)
    (hsafe : (eventRun (serviceCounterModel M J) (x, 0) rs).2.val < J) :
    (rs.map cost).sum < J := by
  rw [service_run_counter] at hsafe
  simp only [Fin.val_zero, zero_add] at hsafe
  have hl : rs.length < J := by omega
  exact lt_of_le_of_lt (event_gross_bound cost hcost rs) hl

end SerialTransferSelection
