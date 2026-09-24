import proofs.FiniteCopyReactor.ChronologicalEndpoint

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability Filter
open scoped ENNReal Topology

theorem elapsed_monotone {α β : Type*} (z : ℕ → JumpState α β)
    (hw : ∀ k,0 ≤ (z (k+1)).2.2) : Monotone (jumpElapsed z) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold jumpElapsed
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (hw k)

theorem endpoint_interval_unique {α β : Type*} (z : ℕ → JumpState α β)
    (hw : ∀ k,0 ≤ (z (k+1)).2.2) (T : ℝ) (i j : ℕ)
    (hi : jumpElapsed z i ≤ T ∧ T < jumpElapsed z (i+1))
    (hj : jumpElapsed z j ≤ T ∧ T < jumpElapsed z (j+1)) : i=j := by
  have hm := elapsed_monotone z hw
  rcases lt_trichotomy i j with h | h | h
  · have he := hm (show i+1 ≤ j by omega)
    linarith [hi.2,hj.1]
  · exact h
  · have he := hm (show j+1 ≤ i by omega)
    linarith [hj.2,hi.1]

theorem endpoint_observable_at {α β : Type*} (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) (hw : ∀ k,0 ≤ (z (k+1)).2.2) (k : ℕ)
    (hk : jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) :
    endpointObservable f T z=f (z k).1 := by
  unfold endpointObservable
  rw [tsum_eq_single k]
  · exact if_pos hk
  · intro j hj
    exact if_neg (fun h => hj (endpoint_interval_unique z hw T j k h hk))

theorem endpoint_observable_le_one {α β : Type*} (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1)
    (T : ℝ) (z : ℕ → JumpState α β) (hw : ∀ k,0 ≤ (z (k+1)).2.2) :
    endpointObservable f T z ≤ 1 := by
  by_cases h : ∃ k,jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)
  · obtain ⟨k,hk⟩ := h
    rw [endpoint_observable_at f T z hw k hk]
    exact hf _
  · have he (k) : ¬(jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) := fun hk => h ⟨k,hk⟩
    simp only [endpointObservable,if_neg (he _),tsum_zero,zero_le]

theorem endpoint_observable_negative {α β : Type*} (f : α → ℝ≥0∞) (T : ℝ) (hT : T < 0)
    (z : ℕ → JumpState α β) (hw : ∀ k,0 ≤ (z (k+1)).2.2) : endpointObservable f T z=0 := by
  have hn (k) : 0 ≤ jumpElapsed z k := Finset.sum_nonneg (fun i _ => hw i)
  have he (k) : ¬(jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) := by
    intro h
    linarith [hn k,h.1]
  simp only [endpointObservable,if_neg (he _),tsum_zero]

theorem endpoint_interval_exists {α β : Type*} (z : ℕ → JumpState α β) (T : ℝ) (hT : 0 ≤ T)
    (hdiv : Tendsto (jumpElapsed z) atTop atTop) :
    ∃ k,jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1) := by
  have hex : ∃ k,T < jumpElapsed z k := by
    obtain ⟨k,hk⟩ := (eventually_atTop.mp (hdiv.eventually (eventually_gt_atTop T)))
    exact ⟨k,hk k le_rfl⟩
  let j := Nat.find hex
  have hj : T < jumpElapsed z j := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro he
    rw [he] at hj
    change T < 0 at hj
    linarith
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  refine ⟨k,?_,?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega : k < j))
  · simpa only [hk] using hj

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem chronological_endpoint_le_one (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (T : ℝ) :
    chronologicalEndpoint next rate hr ht f x T ≤ 1 := by
  have hw := jumpTrajectory_wait_nonneg x next rate hr ht
  have hb : ∀ᵐ z ∂jumpTrajectoryLaw x next rate hr ht,endpointObservable f T z ≤ 1 :=
    hw.mono (fun z hz => endpoint_observable_le_one f hf T z hz)
  exact (lintegral_mono_ae hb).trans_eq (by simp)

theorem chronological_endpoint_negative (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) (hT : T < 0) :
    chronologicalEndpoint next rate hr ht f x T=0 := by
  have hw := jumpTrajectory_wait_nonneg x next rate hr ht
  unfold chronologicalEndpoint
  calc
    _ = ∫⁻ _z,0 ∂jumpTrajectoryLaw x next rate hr ht :=
      lintegral_congr_ae (hw.mono (fun z hz => endpoint_observable_negative f T hT z hz))
    _ = 0 := lintegral_zero

end
end FiniteCopyReactor
