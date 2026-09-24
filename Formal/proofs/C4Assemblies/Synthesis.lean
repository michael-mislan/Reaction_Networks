import proofs.C4Assemblies.Inventory
import proofs.C4Assemblies.Repeated

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def assemblyExport (X : ℝ → Assembly ι) : ℝ := ∫ t in (3:ℝ)..4, totalInventory (X t)

theorem assembly_pulse_inventory (p : ι → Intervention) (c : Assembly ι) :
    totalInventory (assemblyPulse p c)+
      (∑ i, (inventory (withdrawn (p i) (c i))+inventory (lost (p i) (c i)))) = totalInventory c := by
  have hh := congrArg (fun f : ι → ℝ => ∑ i, f i)
    (funext fun i => pulse_inventory_balance (p i) (c i))
  simpa [totalInventory,assemblyPulse,Finset.sum_add_distrib,add_assoc] using hh

theorem assembly_net_lower (P : Parameters ι) (T : ℝ) (hT : 0 ≤ T)
    (p : ι → Intervention) (c : Assembly ι) (hc : ∀ i, Nonneg (c i))
    (X : ℝ → Assembly ι) (h0 : X 0 = assemblyPulse p c)
    (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    totalInventory (X T)-totalInventory c ≤ assemblyNet P.r P.d T X := by
  have hh := assembly_inventory_balance P.k P.exchange_symmetric P.r P.d X T hT hX
  rw [h0] at hh
  have hp := assembly_pulse_inventory p c
  have hr : 0 ≤ ∑ i, (inventory (withdrawn (p i) (c i))+inventory (lost (p i) (c i))) :=
    Finset.sum_nonneg fun i _ => removal_inventory_nonnegative (p i) (c i) (hc i)
  have hi : 0 ≤ ∫ t in (0:ℝ)..T, totalInventory (X t) :=
    intervalIntegral.integral_nonneg hT (fun t ht =>
      Finset.sum_nonneg fun i _ => inventory_nonnegative _ (hn t ht.1 i))
  linarith

theorem assembly_routine_net_lower (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : ∀ i, Nonneg (c i)) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    totalInventory (X 4)-totalInventory c+assemblyExport X ≤ assemblyNet P.r P.d 4 X := by
  have hh := assembly_inventory_balance P.k P.exchange_symmetric P.r P.d X 4 (by norm_num) hX
  rw [h0] at hh
  have hp := assembly_pulse_inventory p c
  have hr : 0 ≤ ∑ i, (inventory (withdrawn (p i) (c i))+inventory (lost (p i) (c i))) :=
    Finset.sum_nonneg fun i _ => removal_inventory_nonnegative (p i) (c i) (hc i)
  have hi (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t => totalInventory (X t)) volume a b :=
    ((show Continuous (@totalInventory ι _) by unfold totalInventory inventory; fun_prop).comp_continuousOn
      (show ContinuousOn X (Icc a b) from fun t ht =>
        (hX t (ha.trans ht.1)).continuousAt.continuousWithinAt)).intervalIntegrable_of_Icc hab
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 3 le_rfl (by norm_num)) (hi 3 4 (by norm_num) (by norm_num))
  have hnon : 0 ≤ ∫ t in (0:ℝ)..3, totalInventory (X t) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t ht =>
      Finset.sum_nonneg fun i _ => inventory_nonnegative _ (hn t ht.1 i))
  dsimp [assemblyExport]
  linarith

theorem assembly_export_lower (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    (Fintype.card ι : ℝ)/28 ≤ assemblyExport X := by
  have hret := (assembly_routine_return P p c hc X h0 hn hX).2
  have hcont : ContinuousOn X (Icc (3:ℝ) 4) := fun t ht =>
    (hX t (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun t => totalInventory (X t)) volume 3 4 :=
    ((show Continuous (@totalInventory ι _) by unfold totalInventory inventory; fun_prop).comp_continuousOn
      hcont).intervalIntegrable_of_Icc (by norm_num)
  have hbound (t : ℝ) (ht : t ∈ Icc (3:ℝ) 4) :
      (Fintype.card ι : ℝ)/28 ≤ totalInventory (X t) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (1/28:ℝ) ≤ inventory (X t i) from by
        have h := inventory_lower (X t i) (hn t (by linarith [ht.1]) i)
        linarith [(hret t ht.1 i).2.2.2])
    simpa [totalInventory,div_eq_mul_inv] using hh
  have hh := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (Fintype.card ι : ℝ)/28) volume 3 4)
    hi hbound
  norm_num [assemblyExport] at hh ⊢
  exact hh

/-- The net-synthesis bound is derived from actual source/pulse histories, not assumed recovery. -/
theorem conditioned_mission_synthesis (P : Parameters ι) (p0 : ι → Intervention)
    (p : ℕ → ι → Intervention) (c : Assembly ι) (hc : AssemblyAdmitted c)
    (C : ℝ → Assembly ι) (s : ℕ → Assembly ι) (X : ℕ → ℝ → Assembly ι)
    (hC0 : C 0 = assemblyPulse p0 c)
    (hCn : ∀ t, 0 ≤ t → ∀ i, Nonneg (C t i))
    (hC : ∀ t, 0 ≤ t → HasDerivAt C (assemblyField P.k P.r P.d (C t)) t)
    (hs0 : s 0 = C 12)
    (h0 : ∀ n, X n 0 = assemblyPulse (p n) (s n))
    (h4 : ∀ n, X n 4 = s (n+1))
    (hn : ∀ n t, 0 ≤ t → ∀ i, Nonneg (X n t i))
    (hX : ∀ n t, 0 ≤ t → HasDerivAt (X n) (assemblyField P.k P.r P.d (X n t)) t) :
    ∀ m : ℕ, (Fintype.card ι : ℝ)*(((m:ℝ)+1)/28-11/10) ≤
      assemblyNet P.r P.d 12 C+∑ n ∈ Finset.range m, assemblyNet P.r P.d 4 (X n) := by
  have hready : ∀ n, AssemblyReady (s n) := by
    intro n
    induction n with
    | zero =>
      rw [hs0]
      exact assembly_conditioning_return P p0 c hc C hC0 hCn hC 12 le_rfl
    | succ n ih =>
      rw [← h4 n]
      exact (assembly_routine_return P (p n) (s n) ih (X n) (h0 n) (hn n) (hX n)).2 4 (by norm_num)
  have hnet (n : ℕ) : totalInventory (s (n+1))-totalInventory (s n)+assemblyExport (X n) ≤
      assemblyNet P.r P.d 4 (X n) := by
    have h := assembly_routine_net_lower P (p n) (s n) (fun i => (hready n i).1)
      (X n) (h0 n) (hn n) (hX n)
    rw [h4 n] at h
    exact h
  have hinit := assembly_net_lower P 12 (by norm_num) p0 c (fun i => (hc i).1) C hC0 hCn hC
  have hupper : totalInventory c ≤ (Fintype.card ι : ℝ)*(11/10) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => inventory_initial_bound (c i) (hc i))
    simpa [totalInventory] using h
  intro m
  have ht := synthesis_telescoping (fun n => totalInventory (s n))
    (fun n => assemblyExport (X n)) (fun n => assemblyNet P.r P.d 4 (X n)) hnet m
  rw [hs0] at ht
  have hout := Finset.sum_le_sum (s := Finset.range m) (fun n _ =>
    assembly_export_lower P (p n) (s n) (hready n) (X n) (h0 n) (hn n) (hX n))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hout
  have hfinal : (Fintype.card ι : ℝ)/28 ≤ totalInventory (s m) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (1/28:ℝ) ≤ inventory (s m i) from by
        have h := inventory_lower (s m i) (hready m i).1
        linarith [(hready m i).2.2.2])
    simpa [totalInventory,div_eq_mul_inv] using hh
  nlinarith

theorem conditioned_threshold (n m : ℕ) (hn : 0 < n) (hm : 30 ≤ m) :
    0 < (n:ℝ)*(((m:ℝ)+1)/28-11/10) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hm' : (30:ℝ) ≤ m := by exact_mod_cast hm
  apply mul_pos hn'
  linarith

theorem ready_threshold (n m : ℕ) (hn : 0 < n) (hm : 28 ≤ m) :
    0 < (n:ℝ)*(((m:ℝ)+1)/28-161/160) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hm' : (28:ℝ) ≤ m := by exact_mod_cast hm
  apply mul_pos hn'
  linarith

end
end C4Assemblies
