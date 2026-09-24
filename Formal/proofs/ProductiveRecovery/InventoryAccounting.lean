import proofs.ProductiveRecovery.OutputSupplies

namespace ProductiveRecovery
noncomputable section
open MeasureTheory

theorem deriv_inventory (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => inventory (X s)) (inventory v) t := by
  have hd := hasDerivAt_pi.1 h
  exact (((hd 2).add (hd 3)).add (hd 4)).add ((hd 5).const_mul 2)

theorem pulse_inventory_balance (p : Intervention) (c : State) :
    inventory (pulse p c) + inventory (withdrawn p c) + inventory (lost p c) = inventory c := by
  have h2 := removal_accounting p c 2
  have h3 := removal_accounting p c 3
  have h4 := removal_accounting p c 4
  have h5 := removal_accounting p c 5
  norm_num [inventory,pulse,Fin.ext_iff]
  linarith

theorem continuous_inventory_balance (r d : ℝ) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    inventory (X 5) + (∫ t in (0:ℝ)..5, inventory (X t)) =
      inventory (X 0) + ∫ t in (0:ℝ)..5,
        flux r d (X t) 0 + flux r d (X t) 3 - flux r d (X t) 5 := by
  have hcont : ContinuousOn X (Set.Icc 0 5) :=
    fun t ht => (hX t ht.1).continuousAt.continuousWithinAt
  have hi : Continuous inventory := by unfold inventory; fun_prop
  have hf : Continuous (fun c => flux r d c 0+flux r d c 3-flux r d c 5) := by
    simp [flux]
    fun_prop
  have hii : IntervalIntegrable (fun t => inventory (X t)) volume 0 5 :=
    (hi.comp_continuousOn hcont).intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 5)
  have hfi : IntervalIntegrable (fun t => flux r d (X t) 0+flux r d (X t) 3-flux r d (X t) 5) volume 0 5 :=
    (hf.comp_continuousOn hcont).intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 5)
  have hd : ∀ t ∈ Set.uIcc (0:ℝ) 5,
      HasDerivAt (fun s => inventory (X s))
        (flux r d (X t) 0+flux r d (X t) 3-flux r d (X t) 5-inventory (X t)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 5 := by simpa using ht
    simpa only [inventory_drift] using deriv_inventory X _ t (hX t ht'.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hfi.sub hii)
  rw [intervalIntegral.integral_sub hfi hii] at h
  linarith

theorem full_cycle_inventory_balance (r d : ℝ) (p : Intervention) (c : State)
    (X : ℝ → State) (h0 : X 0 = pulse p c)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    inventory (X 5) + (∫ t in (0:ℝ)..5, inventory (X t)) +
      inventory (withdrawn p c) + inventory (lost p c) =
      inventory c + ∫ t in (0:ℝ)..5,
        flux r d (X t) 0 + flux r d (X t) 3 - flux r d (X t) 5 := by
  have h := continuous_inventory_balance r d X hX
  rw [h0] at h
  have hp := pulse_inventory_balance p c
  linarith

end
end ProductiveRecovery
