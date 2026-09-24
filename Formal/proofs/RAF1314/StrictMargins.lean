import proofs.C4Assemblies.FineFreeProduct
import proofs.C4Assemblies.OutputSupplies
import proofs.FiniteCopyReactor.Margins

namespace RAF1314
noncomputable section
open ProductiveRecovery C4Assemblies Set MeasureTheory
variable {ι : Type*} [Fintype ι]

/-- Strict stock margin, on the actual coupled source and actual deterministic pulse. -/
theorem strict_network_recovery (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c)
    (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    ∀ t, 11/4 ≤ t → ∀ i, 3/50 ≤ Y (X t i) := by
  have hcor := (assembly_material_bounds P p c
    (fun i => strong_admitted (c i) (hc i)) X h0 hX).1
  have hy0 (i : ι) : 49/4800 ≤ (5/6:ℝ)*Y (X 0 i) := by
    rw [h0]
    have hp := pulse_catalyst (p i) (c i) (hc i).1
    change 49/4800 ≤ (5/6:ℝ)*Y (pulse (p i) (c i))
    linarith [(hc i).2.2.2]
  have he : (1/20:ℝ)/(49/4800) ≤ Real.exp ((3/5)*(11/4)) := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 33/20) 6
    norm_num [Finset.sum_range_succ] at hh ⊢
    linarith
  have hg := assembly_scheduled_recovery
    (fun t i => (5/6:ℝ)*Y (X t i))
    (fun t i => (5/6:ℝ)*Y (assemblyField P.k P.r P.d (X t) i))
    (fun t ht i => (deriv_Y (fun s => X s i) _ t
      (hasDerivAt_pi.1 (hX t ht) i)).const_mul (5/6))
    (49/4800) (11/4) (by norm_num) hy0 (by norm_num) he
    (fun t ht i _ hlow hmin => by
      have hl := FiniteCopyReactor.interior_guarded_growth (P.r i) (P.d i)
        (X t i) (hn t ht i) (P.r_lower i) (P.r_upper i)
        (by linarith [P.d_lower i]) (P.d_upper i)
        (hcor t ht i).1.1 (hcor t ht i).2.1 (by linarith)
      have hm : ∀ j, Y (X t i) ≤ Y (X t j) := by
        intro j
        have hh := hmin j
        linarith
      have hd := diffusion_at_min P.k P.exchange_nonneg (fun j => Y (X t j)) i hm
      dsimp only
      rw [assembly_Y]
      linarith)
  intro t ht i
  have hh := hg t ht i
  linarith

/-- The strengthened stock yields a strict last-unit free-template integral. -/
theorem strict_network_free_output (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c)
    (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    ∀ i, (∀ t ∈ Icc (3:ℝ) 4, 3/400 ≤ X t i 2) ∧
      3/400 ≤ ∫ t in (3:ℝ)..4, X t i 2 := by
  have hcor := (assembly_material_bounds P p c
    (fun i => strong_admitted (c i) (hc i)) X h0 hX).1
  have hy := strict_network_recovery P p c hc X h0 hn hX
  have hf (t : ℝ) (ht : t ∈ Icc (3:ℝ) 4) (i : ι) : 3/400 ≤ X t i 2 := by
    have hh := fine_assembly_free_phase_floor P X hn hX
      (fun s hs j => ⟨(hcor s hs j).1.2, (hcor s hs j).2.2⟩)
      (t-1/28) (3/50) (by linarith [ht.1])
      (hy (t-1/28) (by linarith [ht.1])) i
    norm_num at hh
    simpa only [sub_add_cancel] using hh
  intro i
  refine ⟨fun t ht => hf t ht i, ?_⟩
  have hi : IntervalIntegrable (fun t => X t i 2) volume 3 4 :=
    (show ContinuousOn (fun t => X t i 2) (Icc (3:ℝ) 4) from fun t ht =>
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hX t (by linarith [ht.1])) i) 2).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have hh := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (3/400:ℝ)) volume 3 4)
    hi (fun t ht => hf t ht i)
  norm_num at hh
  exact hh

end
end RAF1314

