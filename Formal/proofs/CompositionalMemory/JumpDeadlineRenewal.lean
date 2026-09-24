import proofs.CompositionalMemory.JumpDeadlineSplit
import proofs.RandomViability.PhysicalRewardRenewal

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def physicalSafeDeadline (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) (initial : α) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ z,safeDeadlinePayoff D f T z ∂jumpTrajectoryLaw initial next rate hr ht

theorem physicalSafeDeadline_le_one (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (initial : α) (T : ℝ) :
    physicalSafeDeadline next rate hr ht D f initial T ≤ 1 := by
  calc
    _ ≤ ∫⁻ _,(1 : ℝ≥0∞) ∂jumpTrajectoryLaw initial next rate hr ht :=
      lintegral_mono (safeDeadlinePayoff_le_one D f hf T)
    _ = 1 := by simp

/-- Renewal for the actual history-preserving deadline payoff, not merely its endpoint. -/
theorem physicalSafeDeadline_renewal (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (D : Set α) (f : α → ℝ≥0∞) (initial : α) (T : ℝ) :
    physicalSafeDeadline next rate hr ht D f initial T =
      if initial ∈ D ∧ 0 ≤ T then
        ∫⁻ y, (if T < y.2 then f initial else 0) +
          physicalSafeDeadline next rate hr ht D f (next initial y.1) (T-y.2)
          ∂jumpClockMeasure (rate initial) (hr initial) (ht initial)
      else 0 := by
  have hm : Measurable (safeDeadlinePayoff D f T : (ℕ → JumpState α β) → ℝ≥0∞) :=
    (safeDeadlinePayoff_measurable D f).comp (measurable_const.prodMk measurable_id)
  unfold physicalSafeDeadline
  rw [jumpTrajectory_first_jump_lintegral initial next rate hr ht _ hm]
  have he (y : β × ℝ) :
      (∫⁻ z,safeDeadlinePayoff D f T z
        ∂Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1
          (firstMarkedPrefix initial next y)) =
        if initial ∈ D ∧ 0 ≤ T then
          (if T < y.2 then f initial else 0) +
            ∫⁻ z,safeDeadlinePayoff D f (T-y.2) z
              ∂jumpTrajectoryLaw (next initial y.1) next rate hr ht
        else 0 := by
    let h1 := firstMarkedPrefix initial next y
    let ν := Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1
    have hp : ∀ᵐ z ∂ν, safeDeadlinePayoff D f T z =
        if initial ∈ D ∧ 0 ≤ T then
          (if T < y.2 then f initial else 0) + safeDeadlinePayoff D f (T-y.2) (restartJump z)
        else 0 := by
      filter_upwards [continuation_prefix_ae next rate hr ht h1] with z hz
      have hz0 : (z 0).1=initial := congrArg Prod.fst (congrFun hz ⟨0,Finset.mem_Iic.mpr (by omega)⟩)
      have hz1 : (z 1).2.2=y.2 := congrArg (fun v => v.2.2)
        (congrFun hz ⟨1,Finset.mem_Iic.mpr le_rfl⟩)
      rw [safeDeadlinePayoff_split,hz0,hz1]
    rw [lintegral_congr_ae hp]
    by_cases h : initial ∈ D ∧ 0 ≤ T
    · simp only [if_pos h]
      rw [lintegral_add_left measurable_const,lintegral_const]
      have hν : ν Set.univ=1 := measure_univ
      rw [hν,mul_one]
      congr 1
      have hm1 : Measurable (safeDeadlinePayoff D f (T-y.2) : (ℕ → JumpState α β) → ℝ≥0∞) :=
        (safeDeadlinePayoff_measurable D f).comp (measurable_const.prodMk measurable_id)
      calc
        _ = ∫⁻ z,safeDeadlinePayoff D f (T-y.2) z ∂ν.map restartJump :=
          (lintegral_map' hm1.aemeasurable restartJump_measurable.aemeasurable).symm
        _ = _ := by rw [jumpTrajectory_restart_law]; rfl
    · simp only [if_neg h,lintegral_zero]
  simp_rw [he]
  by_cases h : initial ∈ D ∧ 0 ≤ T
  · simp only [if_pos h]
  · simp only [if_neg h,lintegral_zero]

end
end CompositionalMemory
