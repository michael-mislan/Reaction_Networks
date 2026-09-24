import proofs.StartupCount.ClockOccupation
import Mathlib.MeasureTheory.Group.LIntegral

namespace StartupCount
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

theorem clock_density_translate (g : ℝ → ℝ≥0∞) (W R τ : ℝ) :
    (∫⁻ u,g (τ+u)*ENNReal.ofReal W*activeClockWeight R u) =
      ∫⁻ t,g t*ENNReal.ofReal W*activeClockWeight R (t-τ) := by
  simpa only [add_sub_cancel_left] using
    (lintegral_add_left_eq_self (μ := volume)
      (fun t => g t*ENNReal.ofReal W*activeClockWeight R (t-τ)) τ)

variable {H : Type*} [MeasurableSpace H]

theorem activeClockWeight_joint (R τ : H → ℝ) (hR : ∀ h,0 < R h)
    (hRm : Measurable R) (hτ : Measurable τ) :
    Measurable (fun p : H × ℝ => activeClockWeight (R p.1) (p.2-τ p.1)) := by
  have he : (fun p : H × ℝ => activeClockWeight (R p.1) (p.2-τ p.1)) =
      fun p => if 0 ≤ p.2-τ p.1 then ENNReal.ofReal (Real.exp (-(R p.1)*(p.2-τ p.1))) else 0 := by
    funext p
    by_cases hp : 0 ≤ p.2-τ p.1
    · rw [activeClockWeight,if_pos hp,if_pos hp,exponential_Ioi _ _ (hR _) hp]
    · rw [activeClockWeight,if_neg hp,if_neg hp]
  rw [he]
  have hu : Measurable (fun p : H × ℝ => p.2-τ p.1) := measurable_snd.sub (hτ.comp measurable_fst)
  exact Measurable.ite (measurableSet_le measurable_const hu)
    ((((hRm.comp measurable_fst).neg.mul hu).exp).ennreal_ofReal) measurable_const

theorem occupation_density_swap (μ : Measure H) [SFinite μ]
    (g : H → ℝ → ℝ≥0∞) (hg : Measurable (fun p : H × ℝ => g p.1 p.2))
    (W R τ : H → ℝ) (hW : Measurable W) (hR : ∀ h,0 < R h)
    (hRm : Measurable R) (hτ : Measurable τ) :
    (∫⁻ h,(∫⁻ t : ℝ,g h t*ENNReal.ofReal (W h)*activeClockWeight (R h) (t-τ h)) ∂μ) =
      ∫⁻ t : ℝ,∫⁻ h,g h t*ENNReal.ofReal (W h)*activeClockWeight (R h) (t-τ h) ∂μ := by
  have hm := (hg.mul ((hW.comp measurable_fst).ennreal_ofReal)).mul
    (activeClockWeight_joint R τ hR hRm hτ)
  exact lintegral_lintegral_swap hm.aemeasurable

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Predictable marked jumps integrated in absolute time. The history is
retained, so time1 is an operating-window endpoint, not a new preparation. -/
theorem history_reward_absolute_occupation (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x j,0 ≤ rate x j) (ht : ∀ x,0 < ∑ j,rate x j)
    (initial : α) (w : α → β → ℝ) (hw : ∀ x j,0 ≤ w x j) (k : ℕ)
    (τ : (Finset.Iic k → JumpState α β) → ℝ) (hτ : Measurable τ)
    (g : (Finset.Iic k → JumpState α β) → ℝ → ℝ≥0∞)
    (hg : Measurable (fun p : (Finset.Iic k → JumpState α β) × ℝ => g p.1 p.2)) :
    (∫⁻ z,ENNReal.ofReal ((z (k+1)).2.1.elim (fun _ => 0) (w (z k).1))*
      g (Preorder.frestrictLe k z) (τ (Preorder.frestrictLe k z)+(z (k+1)).2.2)
      ∂jumpTrajectoryLaw initial next rate hr ht) =
    ∫⁻ t : ℝ,∫⁻ h,g h t*
      ENNReal.ofReal (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j*
        w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)*
      activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j) (t-τ h)
      ∂(jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) := by
  have hg' : Measurable (fun p : (Finset.Iic k → JumpState α β) × ℝ => g p.1 (τ p.1+p.2)) :=
    hg.comp (measurable_fst.prodMk ((hτ.comp measurable_fst).add measurable_snd))
  rw [history_reward_occupation next rate hr ht initial w hw k (fun h u => g h (τ h+u)) hg']
  have he : (∫⁻ h,(∫⁻ u : ℝ,g h (τ h+u)*
      ENNReal.ofReal (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j*w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)*
      activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j) u)
      ∂(jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k)) =
    ∫⁻ h,(∫⁻ t : ℝ,g h t*
      ENNReal.ofReal (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j*w (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j)*
      activeClockWeight (∑ j,rate (h ⟨k,Finset.mem_Iic.mpr le_rfl⟩).1 j) (t-τ h))
      ∂(jumpTrajectoryLaw initial next rate hr ht).map (Preorder.frestrictLe k) := by
    apply lintegral_congr
    intro h
    exact clock_density_translate (g h) _ _ (τ h)
  rw [he]
  apply occupation_density_swap _ g hg _ _ τ _ _ _ hτ
  · exact (measurable_of_countable (fun x => ∑ j,rate x j*w x j)).comp
      (measurable_pi_apply (⟨k,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).fst
  · intro h
    exact ht _
  · exact (measurable_of_countable (fun x => ∑ j,rate x j)).comp
      (measurable_pi_apply (⟨k,Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k)).fst

end
end StartupCount
