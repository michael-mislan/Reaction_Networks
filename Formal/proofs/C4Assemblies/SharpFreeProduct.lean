import proofs.C4Assemblies.SharpPhaseTransfer
import proofs.C4Assemblies.Return
import proofs.ProductiveRecovery.FreeProduct

namespace C4Assemblies
noncomputable section
open ProductiveRecovery Set MeasureTheory
variable {ι : Type*} [Fintype ι]

theorem sharp_assembly_free_phase_floor (P : Parameters ι) (X : ℝ → Assembly ι)
    (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t)
    (hcor : ∀ t, 0 ≤ t → ∀ i, A (X t i) ≤ 11/10 ∧ B (X t i) ≤ 11/10)
    (t b : ℝ) (ht : 0 ≤ t) (hY : ∀ i, b ≤ Y (X t i)) :
    ∀ i, (20/209)*b ≤ X (t+1/24) i 2 := by
  let Z : ℝ → Assembly ι := fun s => X (t+s)
  have hZ (s : ℝ) (hs : 0 ≤ s) : HasDerivAt Z (assemblyField P.k P.r P.d (Z s)) s := by
    have hshift : HasDerivAt (fun v : ℝ => t+v) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_add t
    simpa [Z] using (hX (t+s) (by linarith)).scomp s hshift
  have hcoef (i : ι) : (725/1008)*b ≤ phaseWeight (1/24) (Z 0 i) := by
    have hi := hY i
    have h2 := hn t ht i 2
    have h3 := hn t ht i 3
    have h5 := hn t ht i 5
    dsimp [phaseWeight,Z,Y] at *
    norm_num
    linarith
  have hp := sharp_phase_minimum_propagation P.k P.exchange_nonneg P.r P.d P.r_lower P.r_upper
    (fun i => by linarith [P.d_lower i]) P.d_upper Z (1/24) ((725/1008)*b) (by norm_num)
    (fun s hs => hZ s hs.1)
    (fun s hs i => hn (t+s) (by linarith [hs.1]) i)
    (fun s hs i => (hcor (t+s) (by linarith [hs.1]) i).1)
    (fun s hs i => (hcor (t+s) (by linarith [hs.1]) i).2) hcoef
  have he : Real.exp 2 < 15/2 := by
    have hh : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have heq : Real.exp 2 = Real.exp 1*Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [heq]
    nlinarith [Real.exp_pos 1]
  intro i
  have hh := hp i
  norm_num [Z] at hh
  have hx := hn (t+1/24) (by linarith) i 2
  have hmul := mul_le_mul_of_nonneg_right he.le hx
  nlinarith

theorem sharp_assembly_routine_free_export (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    ∀ i, (∀ t ∈ Icc (3:ℝ) 4, 1/209 ≤ X t i 2) ∧
      1/209 ≤ ∫ t in (3:ℝ)..4, X t i 2 := by
  have hcor := (assembly_material_bounds P p c (fun i => strong_admitted (c i) (hc i)) X h0 hX).1
  have hY := (assembly_routine_return P p c hc X h0 hn hX).1
  have hfloor (t : ℝ) (ht : t ∈ Icc (3:ℝ) 4) (i : ι) : 1/209 ≤ X t i 2 := by
    have h := sharp_assembly_free_phase_floor P X hn hX
      (fun s hs j => ⟨(hcor s hs j).1.2,(hcor s hs j).2.2⟩) (t-1/24) (1/20)
      (by linarith [ht.1]) (hY (t-1/24) (by linarith [ht.1])) i
    norm_num at h
    simpa only [sub_add_cancel] using h
  intro i
  refine ⟨fun t ht => hfloor t ht i,?_⟩
  have hi : IntervalIntegrable (fun t => X t i 2) volume 3 4 :=
    (show ContinuousOn (fun t => X t i 2) (Icc (3:ℝ) 4) from fun t ht =>
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hX t (by linarith [ht.1])) i) 2).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have h := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/209:ℝ)) volume 3 4)
    hi (fun t ht => hfloor t ht i)
  norm_num at h
  exact h

end
end C4Assemblies
