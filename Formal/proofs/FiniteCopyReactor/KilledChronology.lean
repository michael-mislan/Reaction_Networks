import proofs.FiniteCopyReactor.KilledObservable

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def killedChronologicalEndpoint (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ z,killedEndpointObservable D f T z ∂jumpTrajectoryLaw x next rate hr ht

theorem killed_chronological_measurable (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b) (f : α → ℝ≥0∞) :
    Measurable (fun p : ℝ × α => killedChronologicalEndpoint D next rate hr ht f p.2 p.1) := by
  apply measurable_from_prod_countable_left
  intro x
  change Measurable (fun T => ∫⁻ z,killedEndpointObservable (β := β) D f T z ∂jumpTrajectoryLaw x next rate hr ht)
  exact (killed_observable_measurable (β := β) D f).lintegral_prod_right'

theorem killed_chronological_le (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) :
    killedChronologicalEndpoint D next rate hr ht f x T ≤ chronologicalEndpoint next rate hr ht f x T :=
  lintegral_mono (killed_observable_le D f T)

theorem killed_chronological_le_one (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (T : ℝ) :
    killedChronologicalEndpoint D next rate hr ht f x T ≤ 1 :=
  (killed_chronological_le D next rate hr ht f x T).trans
    (chronological_endpoint_le_one next rate hr ht f hf x T)

theorem killed_chronological_negative (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) (hT : T < 0) :
    killedChronologicalEndpoint D next rate hr ht f x T=0 :=
  le_antisymm ((killed_chronological_le D next rate hr ht f x T).trans_eq
    (chronological_endpoint_negative next rate hr ht f x T hT)) bot_le

/-- Exact first-jump equation for the original trajectory killed at its first exit. -/
theorem killed_chronological_renewal (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) :
    killedChronologicalEndpoint D next rate hr ht f x T=if x ∈ D then
      ∫⁻ y,(if 0 ≤ T ∧ T < y.2 then f x else 0)+
        killedChronologicalEndpoint D next rate hr ht f (next x y.1) (T-y.2)
        ∂jumpClockMeasure (rate x) (hr x) (ht x) else 0 := by
  have hm (t : ℝ) : Measurable (killedEndpointObservable (β := β) D f t) :=
    (killed_observable_measurable D f).comp (measurable_const.prodMk measurable_id)
  have hcont (y : β × ℝ) :
      (∫⁻ z,killedEndpointObservable D f T z ∂Kernel.traj (X := fun _ => JumpState α β)
        (jumpHistoryKernel next rate hr ht) 1 (firstMarkedPrefix x next y))=
      if x ∈ D then (if 0 ≤ T ∧ T < y.2 then f x else 0)+
        killedChronologicalEndpoint D next rate hr ht f (next x y.1) (T-y.2) else 0 := by
    let h1 := firstMarkedPrefix x next y
    let ν := Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1
    letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    have he : ∀ᵐ z ∂ν,killedEndpointObservable D f T z=if x ∈ D then
        (if 0 ≤ T ∧ T < y.2 then f x else 0)+killedEndpointObservable D f (T-y.2) (restartJump z) else 0 := by
      filter_upwards [continuation_prefix_ae next rate hr ht h1] with z hz
      have hz0 : z 0=(x,(Sum.inl (), (0:ℝ))) := congrFun hz ⟨0,Finset.mem_Iic.mpr (by omega)⟩
      have hz1 : z 1=jumpStateUpdate next x y := congrFun hz ⟨1,Finset.mem_Iic.mpr le_rfl⟩
      rw [killed_observable_split,hz0,hz1]
      rfl
    change (∫⁻ z,killedEndpointObservable D f T z ∂ν)=_
    rw [lintegral_congr_ae he]
    by_cases hx : x ∈ D
    · simp only [if_pos hx]
      rw [lintegral_add_left measurable_const,lintegral_const]
      simp only [measure_univ,mul_one]
      congr 1
      rw [← lintegral_map' (hm (T-y.2)).aemeasurable restartJump_measurable.aemeasurable,
        jumpTrajectory_restart_law]
      rfl
    · simp only [if_neg hx,lintegral_zero]
  change (∫⁻ z,killedEndpointObservable D f T z ∂jumpTrajectoryLaw x next rate hr ht)=_
  rw [jumpTrajectory_first_jump_lintegral x next rate hr ht _ (hm T)]
  calc
    _ = ∫⁻ y,(if x ∈ D then (if 0 ≤ T ∧ T < y.2 then f x else 0)+
        killedChronologicalEndpoint D next rate hr ht f (next x y.1) (T-y.2) else 0)
        ∂jumpClockMeasure (rate x) (hr x) (ht x) := lintegral_congr hcont
    _ = _ := by by_cases hx : x ∈ D <;> simp only [hx,if_true,if_false,lintegral_zero]

theorem killed_chronological_outside (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) (hx : x ∉ D) :
    killedChronologicalEndpoint D next rate hr ht f x T=0 := by
  rw [killed_chronological_renewal,if_neg hx]

end
end FiniteCopyReactor
