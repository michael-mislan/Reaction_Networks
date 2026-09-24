import proofs.SerialTransferSelection.ServiceCounter
import proofs.ResourceLimitedCompetition.ProbabilityUnion

namespace SerialTransferSelection
open FiniteCopy ResourceLimitedCompetition
open scoped NNReal

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
  (M : FiniteJumpModel α β) (J : ℕ)

theorem service_quota_bound (hJ : 0 < J) (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hb : ∀ x, M.total x ≤ q) (x : α) :
    ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).poissonized
      (q*t) (FiniteKernel.eventIndicator {s | s.2.val = J}) (x, 0) ≤ (t : ℝ)*q/J := by
  apply (le_div_iff₀ (show (0 : ℝ) < J by exact_mod_cast hJ)).mpr
  simpa only [mul_comm] using service_quota_scaled_bound M J q t hq hb x

/-- Source success and finite event service hold on one joint law; no conditioning
discards quota failures. -/
theorem service_joint_lower (hJ : 0 < J) (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hb : ∀ x, M.total x ≤ q) (A : Set α) (x : α) :
    (M.uniformize q hq hb).poissonized (q*t) (FiniteKernel.eventIndicator A) x -
        (t : ℝ)*q/J ≤
      ((serviceCounterModel M J).uniformize q hq (fun z => hb z.1)).poissonized
        (q*t) (FiniteKernel.eventIndicator {s | s.1 ∈ A ∧ s.2.val < J}) (x, 0) := by
  classical
  let P := (serviceCounterModel M J).uniformize q hq (fun z => hb z.1)
  let G : Set (α × Fin (J+1)) := {s | s.1 ∈ A ∧ s.2.val < J}
  let B : Set (α × Fin (J+1)) := {s | s.2.val = J}
  have hp (s : α × Fin (J+1)) : FiniteKernel.eventIndicator A s.1 ≤
      FiniteKernel.eventIndicator G s + FiniteKernel.eventIndicator B s := by
    have hc := s.2.isLt
    simp only [FiniteKernel.eventIndicator, G, B, Set.mem_setOf_eq]
    split_ifs <;> simp_all
    omega
  have hm := P.poissonized_mono (q*t) (fun s => FiniteKernel.eventIndicator A s.1)
    (fun s => FiniteKernel.eventIndicator G s+FiniteKernel.eventIndicator B s)
    (fun s => event_indicator_nonneg A s.1)
    (fun s => add_nonneg (event_indicator_nonneg G s) (event_indicator_nonneg B s)) hp (x, 0)
  rw [P.poissonized_add _ _ _ (event_indicator_nonneg G) (event_indicator_nonneg B)] at hm
  have he := service_poissonized_projection M J q hq hb (q*t)
    (FiniteKernel.eventIndicator A) (x, 0)
  have hquota := service_quota_bound M J hJ q t hq hb x
  change P.poissonized (q*t) (FiniteKernel.eventIndicator B) (x, 0) ≤ _ at hquota
  change P.poissonized (q*t) (fun s => FiniteKernel.eventIndicator A s.1) (x, 0) = _ at he
  rw [he] at hm
  change _ ≤ P.poissonized (q*t) (FiniteKernel.eventIndicator G) (x, 0)
  linarith

theorem exists_finite_service_quota (q t δ : ℝ) (hδ : 0 < δ) :
    ∃ J : ℕ, 0 < J ∧ t*q/(J : ℝ) < δ := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (max (t*q/δ) 0)
  have hpos : (0 : ℝ) < J := lt_of_le_of_lt (le_max_right _ _) hJ
  refine ⟨J, by exact_mod_cast hpos, ?_⟩
  apply (div_lt_iff₀ hpos).mpr
  have hh := (div_lt_iff₀ hδ).mp (lt_of_le_of_lt (le_max_left _ _) hJ)
  linarith

end SerialTransferSelection
