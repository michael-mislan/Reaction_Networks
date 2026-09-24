import proofs.C4Assemblies.FreeProduct

namespace C4Assemblies
noncomputable section
open ProductiveRecovery Set MeasureTheory
variable {ι : Type*} [Fintype ι]

theorem assembly_routine_output_supplies (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    ∀ i, 1/28 ≤ routineExport (fun t => X t i) ∧
      routineFoodU (p i) ≤ 951/200 ∧ routineFoodW (p i) ≤ 951/200 ∧
      routineService (P.d i) (fun t => X t i) ≤ 9/50 := by
  have hcor := (assembly_material_bounds P p c (fun i => strong_admitted (c i) (hc i)) X h0 hX).1
  have hret := (assembly_routine_return P p c hc X h0 hn hX).2
  intro i
  have hcont (a b : ℝ) (ha : 0 ≤ a) : ContinuousOn (fun t => X t i) (Icc a b) :=
    fun t ht => (hasDerivAt_pi.1 (hX t (ha.trans ht.1)) i).continuousAt.continuousWithinAt
  have hi : Continuous inventory := by unfold inventory; fun_prop
  have hi34 : IntervalIntegrable (fun t => inventory (X t i)) volume 3 4 :=
    (hi.comp_continuousOn (hcont 3 4 (by norm_num))).intervalIntegrable_of_Icc (by norm_num)
  have ho := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/28:ℝ)) volume 3 4)
    hi34 (fun t ht => by
      have hh := inventory_lower (X t i) (hn t (by linarith [ht.1]) i)
      have hy := (hret t ht.1 i).2.2.2
      linarith)
  have hg : Continuous (fun c : State => P.d i*c 2+P.d i*(1/8000000000)*c 0*c 1) := by fun_prop
  have hg04 : IntervalIntegrable (fun t => P.d i*X t i 2+P.d i*(1/8000000000)*X t i 0*X t i 1) volume 0 4 :=
    (hg.comp_continuousOn (hcont 0 4 le_rfl)).intervalIntegrable_of_Icc (by norm_num)
  have hs := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 4) (by norm_num) hg04
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (9/200:ℝ)) volume 0 4)
    (fun t ht => gross_service_bound (P.d i) (X t i) (hn t ht.1 i) (P.d_upper i)
      (hcor t ht.1 i).1.2 (hcor t ht.1 i).2.2)
  obtain ⟨_,hu,_,hw⟩ := food_feasible (p i)
  refine ⟨?_,?_,?_,?_⟩
  · norm_num [intervalIntegral.integral_const] at ho
    exact ho
  · dsimp [routineFoodU]; linarith
  · dsimp [routineFoodW]; linarith
  · norm_num [intervalIntegral.integral_const] at hs
    exact hs

end
end C4Assemblies
