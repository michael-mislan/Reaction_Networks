import proofs.ProductiveRecovery.InventoryAccounting
import proofs.ProductiveRecovery.ConditionedOperation
namespace ProductiveRecovery
noncomputable section
open MeasureTheory Set
theorem inventory_balance_over (r d T : ℝ) (hT : 0 ≤ T) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    inventory (X T) + (∫ t in (0:ℝ)..T, inventory (X t)) =
      inventory (X 0) + ∫ t in (0:ℝ)..T,
        flux r d (X t) 0 + flux r d (X t) 3 - flux r d (X t) 5 := by
  have hcont : ContinuousOn X (Set.Icc 0 T) :=
    fun t ht => (hX t ht.1).continuousAt.continuousWithinAt
  have hi : Continuous inventory := by unfold inventory; fun_prop
  have hf : Continuous (fun c => flux r d c 0+flux r d c 3-flux r d c 5) := by
    simp [flux]
    fun_prop
  have hii : IntervalIntegrable (fun t => inventory (X t)) volume 0 T :=
    (hi.comp_continuousOn hcont).intervalIntegrable_of_Icc hT
  have hfi : IntervalIntegrable (fun t => flux r d (X t) 0+flux r d (X t) 3-flux r d (X t) 5) volume 0 T :=
    (hf.comp_continuousOn hcont).intervalIntegrable_of_Icc hT
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun s => inventory (X s))
        (flux r d (X t) 0+flux r d (X t) 3-flux r d (X t) 5-inventory (X t)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) T := by simpa [Set.uIcc_of_le hT] using ht
    simpa only [inventory_drift] using deriv_inventory X _ t (hX t ht'.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hfi.sub hii)
  rw [intervalIntegral.integral_sub hfi hii] at h
  linarith

theorem pulse_balance_over (r d T : ℝ) (hT : 0 ≤ T) (p : Intervention) (c : State)
    (X : ℝ → State) (h0 : X 0 = pulse p c)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    inventory (X T) + (∫ t in (0:ℝ)..T, inventory (X t)) +
      inventory (withdrawn p c) + inventory (lost p c) =
      inventory c + ∫ t in (0:ℝ)..T,
        flux r d (X t) 0 + flux r d (X t) 3 - flux r d (X t) 5 := by
  have h := inventory_balance_over r d T hT X hX
  rw [h0] at h
  have hp := pulse_inventory_balance p c
  linarith

theorem inventory_nonnegative (c : State) (hc : Nonneg c) : 0 ≤ inventory c := by
  dsimp [inventory]
  linarith [hc 2,hc 3,hc 4,hc 5]

theorem inventory_initial_bound (c : State) (hc : Admitted c) : inventory c ≤ 11/10 := by
  have ha := hc.2.1.2
  dsimp [inventory,A] at *
  linarith [hc.1 0,hc.1 3,hc.1 4]

def netOver (r d T : ℝ) (X : ℝ → State) : ℝ :=
  ∫ t in (0:ℝ)..T, flux r d (X t) 0+flux r d (X t) 3-flux r d (X t) 5

theorem removal_inventory_nonnegative (p : Intervention) (c : State) (hc : Nonneg c) :
    0 ≤ inventory (withdrawn p c)+inventory (lost p c) := by
  have hw : Nonneg (withdrawn p c) := by
    intro i
    exact mul_nonneg (by linarith [p.q_upper]) (hc i)
  have hl : Nonneg (lost p c) := by
    intro i
    exact mul_nonneg (mul_nonneg (by linarith [p.q_lower])
      (by linarith [p.loss_upper i])) (hc i)
  linarith [inventory_nonnegative _ hw,inventory_nonnegative _ hl]

theorem net_over_lower (r d T : ℝ) (hT : 0 ≤ T) (p : Intervention) (c : State)
    (hc : Nonneg c) (X : ℝ → State) (h0 : X 0 = pulse p c)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    inventory (X T)-inventory c ≤ netOver r d T X := by
  have h := pulse_balance_over r d T hT p c X h0 hX
  have hi : 0 ≤ ∫ t in (0:ℝ)..T, inventory (X t) :=
    intervalIntegral.integral_nonneg hT (fun t ht => inventory_nonnegative _ (hn t ht.1))
  have hp := removal_inventory_nonnegative p c hc
  dsimp [netOver]
  linarith

theorem routine_net_lower (r d : ℝ) (p : Intervention) (c : State)
    (hc : Nonneg c) (X : ℝ → State) (h0 : X 0 = pulse p c)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    inventory (X 4)-inventory c+routineExport X ≤ netOver r d 4 X := by
  have h := pulse_balance_over r d 4 (by norm_num) p c X h0 hX
  have hi (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t => inventory (X t)) volume a b :=
    ((show Continuous inventory by unfold inventory; fun_prop).comp_continuousOn
      (show ContinuousOn X (Icc a b) from fun t ht =>
        (hX t (ha.trans ht.1)).continuousAt.continuousWithinAt)).intervalIntegrable_of_Icc hab
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 3 le_rfl (by norm_num)) (hi 3 4 (by norm_num) (by norm_num))
  have hnon : 0 ≤ ∫ t in (0:ℝ)..3, inventory (X t) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t ht => inventory_nonnegative _ (hn t ht.1))
  have hp := removal_inventory_nonnegative p c hc
  dsimp [netOver,routineExport]
  linarith

theorem synthesis_telescoping (s q p : ℕ → ℝ)
    (h : ∀ n, s (n+1)-s n+q n ≤ p n) (m : ℕ) :
    s m-s 0+∑ n ∈ Finset.range m, q n ≤ ∑ n ∈ Finset.range m, p n := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Finset.sum_range_succ]
    linarith [h m]

end
end ProductiveRecovery
