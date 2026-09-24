import proofs.RandomViability.PhysicalRewardRenewal
import proofs.RandomViability.JumpWaitingSupport

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

def endpointObservable {α β : Type*} (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) : ℝ≥0∞ :=
  ∑' k, if jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1) then f (z k).1 else 0

theorem endpoint_observable_split {α β : Type*} (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) :
    endpointObservable f T z=(if 0 ≤ T ∧ T < (z 1).2.2 then f (z 0).1 else 0)+
      endpointObservable f (T-(z 1).2.2) (restartJump z) := by
  unfold endpointObservable
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : jumpElapsed z 0=0 := rfl
  have h1 : jumpElapsed z (0+1)=(z 1).2.2 := by simp [jumpElapsed]
  rw [h0,h1]
  congr 1
  apply tsum_congr
  intro k
  have he (l : ℕ) : jumpElapsed z (l+1)=(z 1).2.2+jumpElapsed (restartJump z) l :=
    restart_wait_sum z l
  have hx : (restartJump z k).1=(z (k+1)).1 := by cases k <;> rfl
  rw [he k,he (k+1),hx]
  have ht : (z 1).2.2+jumpElapsed (restartJump z) k ≤ T ∧
      T < (z 1).2.2+jumpElapsed (restartJump z) (k+1) ↔
      jumpElapsed (restartJump z) k ≤ T-(z 1).2.2 ∧
      T-(z 1).2.2 < jumpElapsed (restartJump z) (k+1) := by constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  simp only [ht]

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [Fintype β] [MeasurableSingletonClass β] in
theorem endpoint_observable_measurable (f : α → ℝ≥0∞) :
    Measurable (fun p : ℝ × (ℕ → JumpState α β) => endpointObservable f p.1 p.2) := by
  unfold endpointObservable
  apply Measurable.tsum
  intro k
  exact Measurable.ite
    ((measurableSet_le ((jumpElapsed_measurable k).comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst ((jumpElapsed_measurable (k+1)).comp measurable_snd)))
    ((measurable_of_countable f).comp ((measurable_pi_apply k).comp measurable_snd).fst) measurable_const

def chronologicalEndpoint (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ z,endpointObservable f T z ∂jumpTrajectoryLaw x next rate hr ht

theorem chronological_endpoint_renewal (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) :
    chronologicalEndpoint next rate hr ht f x T =
      ∫⁻ y, (if 0 ≤ T ∧ T < y.2 then f x else 0)+
        chronologicalEndpoint next rate hr ht f (next x y.1) (T-y.2)
        ∂jumpClockMeasure (rate x) (hr x) (ht x) := by
  have hm (t : ℝ) : Measurable (endpointObservable (β := β) f t) :=
    (endpoint_observable_measurable f).comp (measurable_const.prodMk measurable_id)
  unfold chronologicalEndpoint
  rw [jumpTrajectory_first_jump_lintegral x next rate hr ht _ (hm T)]
  apply lintegral_congr
  intro y
  let h1 := firstMarkedPrefix x next y
  let ν := Kernel.traj (X := fun _ => JumpState α β) (jumpHistoryKernel next rate hr ht) 1 h1
  letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have he : ∀ᵐ z ∂ν,endpointObservable f T z=
      (if 0 ≤ T ∧ T < y.2 then f x else 0)+endpointObservable f (T-y.2) (restartJump z) := by
    filter_upwards [continuation_prefix_ae next rate hr ht h1] with z hz
    have hz0 : z 0=(x,(Sum.inl (), (0:ℝ))) := congrFun hz ⟨0,Finset.mem_Iic.mpr (by omega)⟩
    have hz1 : z 1=jumpStateUpdate next x y := congrFun hz ⟨1,Finset.mem_Iic.mpr le_rfl⟩
    rw [endpoint_observable_split,hz0,hz1]
    rfl
  change (∫⁻ z,endpointObservable f T z ∂ν)=_
  rw [lintegral_congr_ae he,lintegral_add_left measurable_const,lintegral_const]
  simp only [measure_univ,mul_one]
  congr 1
  rw [← lintegral_map' (hm (T-y.2)).aemeasurable restartJump_measurable.aemeasurable]
  rw [jumpTrajectory_restart_law]
  rfl

end
end FiniteCopyReactor
