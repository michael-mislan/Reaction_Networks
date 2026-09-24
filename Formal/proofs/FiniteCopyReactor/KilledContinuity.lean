import proofs.FiniteCopyReactor.KilledExhaustion

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

theorem killed_observable_mono_payoff {α β : Type*} (D : Set α) (f g : α → ℝ≥0∞)
    (hfg : ∀ x,f x ≤ g x) (T : ℝ) (z : ℕ → JumpState α β) :
    killedEndpointObservable D f T z ≤ killedEndpointObservable D g T z := by
  apply ENNReal.tsum_le_tsum
  intro k
  split_ifs
  · exact hfg _
  · exact le_rfl

theorem killed_observable_iSup {α β : Type*} (D : Set α) (f : ℕ → α → ℝ≥0∞)
    (T : ℝ) (z : ℕ → JumpState α β) (hw : ∀ k,0 ≤ (z (k+1)).2.2) :
    killedEndpointObservable D (fun y => ⨆ n,f n y) T z=⨆ n,killedEndpointObservable D (f n) T z := by
  by_cases h : ∃ k,(jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) ∧ prefixAlive D k z
  · obtain ⟨k,hk,hD⟩ := h
    simp_rw [killed_observable_at D _ T z hw k hk hD]
  · have he (k) : ¬((jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) ∧ prefixAlive D k z) :=
      fun hk => h ⟨k,hk⟩
    simp only [killedEndpointObservable,if_neg (he _),tsum_zero,iSup_const]

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem killed_chronological_mono_payoff (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f g : α → ℝ≥0∞) (hfg : ∀ x,f x ≤ g x) (x : α) (T : ℝ) :
    killedChronologicalEndpoint D next rate hr ht f x T ≤
      killedChronologicalEndpoint D next rate hr ht g x T :=
  lintegral_mono (killed_observable_mono_payoff D f g hfg T)

theorem killed_chronological_mono_region (D E : Set α) (hDE : D ⊆ E)
    (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) :
    killedChronologicalEndpoint D next rate hr ht f x T ≤
      killedChronologicalEndpoint E next rate hr ht f x T :=
  lintegral_mono (killed_observable_mono_region D E hDE f T)

theorem killed_chronological_iSup (D : Set α) (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : ℕ → α → ℝ≥0∞) (hf : Monotone f) (x : α) (T : ℝ) :
    killedChronologicalEndpoint D next rate hr ht (fun y => ⨆ n,f n y) x T=
      ⨆ n,killedChronologicalEndpoint D next rate hr ht (f n) x T := by
  have hm (n : ℕ) : Measurable (killedEndpointObservable (β := β) D (f n) T) :=
    (killed_observable_measurable D (f n)).comp (measurable_const.prodMk measurable_id)
  have hmono : Monotone (fun n => killedEndpointObservable (β := β) D (f n) T) := by
    intro n m hnm z
    exact killed_observable_mono_payoff D _ _ (hf hnm) T z
  unfold killedChronologicalEndpoint
  rw [← lintegral_iSup hm hmono]
  apply lintegral_congr_ae
  filter_upwards [jumpTrajectory_wait_nonneg x next rate hr ht] with z hz
  exact killed_observable_iSup D f T z hz

end
end FiniteCopyReactor
