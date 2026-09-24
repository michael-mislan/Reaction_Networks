import proofs.C4Assemblies.SharedAccounts

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def sharedServicePrefix (P : Parameters ι) (X : ℝ → Assembly ι) (t : ℝ) : ℝ :=
  ∑ i, ∫ s in (0:ℝ)..t, P.d i*X s i 2+P.d i*(1/8000000000)*X s i 0*X s i 1
def sharedFoodUPrefix (p : ι → Intervention) (t : ℝ) : ℝ := ∑ i, (1-(p i).q+(p i).eU+t)
def sharedFoodWPrefix (p : ι → Intervention) (t : ℝ) : ℝ := ∑ i, (1-(p i).q+(p i).eW+t)

theorem source_prefix_allowances (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t)
    (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    sharedFoodUPrefix p t ≤ (Fintype.card ι : ℝ)*(T+151/200) ∧
    sharedFoodWPrefix p t ≤ (Fintype.card ι : ℝ)*(T+151/200) ∧
    sharedServicePrefix P X t ≤ (Fintype.card ι : ℝ)*(9/200)*T := by
  have hcor := (assembly_material_bounds P p c hc X h0 hX).1
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show 1-(p i).q+(p i).eU+t ≤ T+151/200 from by
      have hh := (food_feasible (p i)).2.1
      linarith)
  have hw := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show 1-(p i).q+(p i).eW+t ≤ T+151/200 from by
      have hh := (food_feasible (p i)).2.2.2
      linarith)
  have hg (i : ι) : (∫ s in (0:ℝ)..t,
      P.d i*X s i 2+P.d i*(1/8000000000)*X s i 0*X s i 1) ≤ (9/200)*T := by
    have hcont : ContinuousOn (fun s => X s i) (Icc 0 t) := fun s hs =>
      (hasDerivAt_pi.1 (hX s hs.1) i).continuousAt.continuousWithinAt
    have hg : Continuous (fun c : State => P.d i*c 2+P.d i*(1/8000000000)*c 0*c 1) := by fun_prop
    have hi : IntervalIntegrable (fun s => P.d i*X s i 2+
        P.d i*(1/8000000000)*X s i 0*X s i 1) volume 0 t :=
      (hg.comp_continuousOn hcont).intervalIntegrable_of_Icc ht
    have hh := intervalIntegral.integral_mono_on ht hi
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (9/200:ℝ)) volume 0 t)
      (fun s hs => gross_service_bound (P.d i) (X s i) (hn s hs.1 i) (P.d_upper i)
        (hcor s hs.1 i).1.2 (hcor s hs.1 i).2.2)
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hg i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hu hw hsum
  exact ⟨hu,hw,by simpa [sharedServicePrefix,mul_assoc] using hsum⟩

theorem source_transport_allowance (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, grossTransfer P.k (X t)) ≤ T*(11/5)*(∑ i, ∑ j, P.k i j) := by
  have hcor := (assembly_material_bounds P p c hc X h0 hX).1
  have hcX : ContinuousOn X (Icc 0 T) := fun t ht => (hX t ht.1).continuousAt.continuousWithinAt
  have hcG : Continuous (grossTransfer P.k) := by unfold grossTransfer; fun_prop
  have hi : IntervalIntegrable (fun t => grossTransfer P.k (X t)) volume 0 T :=
    (hcG.comp_continuousOn hcX).intervalIntegrable_of_Icc hT
  have hh := intervalIntegral.integral_mono_on hT hi
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (11/5)*(∑ i, ∑ j, P.k i j)) volume 0 T)
    (fun t ht => gross_transfer_bound P.k P.exchange_nonneg (X t) (hn t ht.1)
      (fun i => (hcor t ht.1 i).1.2) (fun i => (hcor t ht.1 i).2.2))
  convert hh using 1
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  ring

/-- Explicit prefix allocation for one common account, including the live cycle. -/
theorem common_mission_prefix_allowance (n m k : ℕ) (hkm : k < m)
    (conditioning spent live : ℝ) (C R : ℝ) (hR : 0 ≤ R)
    (hcond : conditioning ≤ (n:ℝ)*C) (hspent : spent ≤ (n:ℝ)*R*(k:ℝ))
    (hlive : live ≤ (n:ℝ)*R) :
    conditioning+spent+live ≤ (n:ℝ)*(C+R*(m:ℝ)) := by
  have hk : (k:ℝ)+1 ≤ m := by exact_mod_cast hkm
  have hprod := mul_nonneg (show (0:ℝ) ≤ n by positivity) hR
  nlinarith

def maintainedWithCutoff {E : Type*} [Zero E] (field : E)
    (U W G quotaU quotaW quotaG : ℝ) : E :=
  if U ≤ quotaU ∧ W ≤ quotaW ∧ G ≤ quotaG then field else 0

theorem allocated_cutoff_agrees {E : Type*} [Zero E] (field : E)
    (U W G quotaU quotaW quotaG : ℝ)
    (hU : U ≤ quotaU) (hW : W ≤ quotaW) (hG : G ≤ quotaG) :
    maintainedWithCutoff field U W G quotaU quotaW quotaG = field := by
  simp [maintainedWithCutoff,hU,hW,hG]

end
end C4Assemblies
