import proofs.C4Assemblies.FinePhaseTransfer
import proofs.C4Assemblies.Return
import proofs.ProductiveRecovery.FreeProduct

namespace C4Assemblies
noncomputable section
open ProductiveRecovery Set MeasureTheory
variable {ι : Type*} [Fintype ι]

/-- Truncated Taylor bound `exp(6/7) ≤ 2.357` from Mathlib's `Real.exp_bound'`
with eight terms, squared to `exp(12/7) ≤ 961355/172872`. -/
theorem fine_exp_twelve_sevenths : Real.exp (12/7) ≤ 961355/172872 := by
  have h1 : Real.exp (6/7) ≤ (∑ m ∈ Finset.range 8, (6/7:ℝ)^m/(m.factorial:ℝ)) +
      (6/7:ℝ)^8*((8:ℕ)+1)/(((8:ℕ).factorial:ℝ)*(8:ℕ)) :=
    Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
  have h2 : (∑ m ∈ Finset.range 8, (6/7:ℝ)^m/(m.factorial:ℝ)) +
      (6/7:ℝ)^8*((8:ℕ)+1)/(((8:ℕ).factorial:ℝ)*(8:ℕ)) ≤ 2357/1000 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have h3 : Real.exp (6/7) ≤ 2357/1000 := h1.trans h2
  have heq : Real.exp (12/7) = Real.exp (6/7)*Real.exp (6/7) := by
    rw [← Real.exp_add]; norm_num
  rw [heq]
  nlinarith [Real.exp_pos (6/7)]

theorem fine_assembly_free_phase_floor (P : Parameters ι) (X : ℝ → Assembly ι)
    (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t)
    (hcor : ∀ t, 0 ≤ t → ∀ i, A (X t i) ≤ 11/10 ∧ B (X t i) ≤ 11/10)
    (t b : ℝ) (ht : 0 ≤ t) (hY : ∀ i, b ≤ Y (X t i)) :
    ∀ i, (1/8)*b ≤ X (t+1/28) i 2 := by
  let Z : ℝ → Assembly ι := fun s => X (t+s)
  have hZ (s : ℝ) (hs : 0 ≤ s) : HasDerivAt Z (assemblyField P.k P.r P.d (Z s)) s := by
    have hshift : HasDerivAt (fun v : ℝ => t+v) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_add t
    simpa [Z] using (hX (t+s) (by linarith)).scomp s hshift
  have hcoef (i : ι) : (961355/1382976)*b ≤ finePhaseWeight (1/28) (Z 0 i) := by
    have hi := hY i
    have h2 := hn t ht i 2
    have h4 := hn t ht i 4
    have h5 := hn t ht i 5
    dsimp [finePhaseWeight,Z,Y] at *
    norm_num
    linarith
  have hp := fine_phase_minimum_propagation P.k P.exchange_nonneg P.r P.d P.r_lower P.r_upper
    (fun i => by linarith [P.d_lower i]) P.d_upper Z (1/28) ((961355/1382976)*b) (by norm_num)
    (fun s hs => hZ s hs.1)
    (fun s hs i => hn (t+s) (by linarith [hs.1]) i)
    (fun s hs i => (hcor (t+s) (by linarith [hs.1]) i).1)
    (fun s hs i => (hcor (t+s) (by linarith [hs.1]) i).2) hcoef
  have he := fine_exp_twelve_sevenths
  intro i
  have hh := hp i
  norm_num [Z] at hh
  have hx := hn (t+1/28) (by linarith) i 2
  have hmul := mul_le_mul_of_nonneg_right he hx
  linarith

theorem fine_assembly_routine_free_export (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    ∀ i, (∀ t ∈ Icc (3:ℝ) 4, 1/160 ≤ X t i 2) ∧
      1/160 ≤ ∫ t in (3:ℝ)..4, X t i 2 := by
  have hcor := (assembly_material_bounds P p c (fun i => strong_admitted (c i) (hc i)) X h0 hX).1
  have hY := (assembly_routine_return P p c hc X h0 hn hX).1
  have hfloor (t : ℝ) (ht : t ∈ Icc (3:ℝ) 4) (i : ι) : 1/160 ≤ X t i 2 := by
    have h := fine_assembly_free_phase_floor P X hn hX
      (fun s hs j => ⟨(hcor s hs j).1.2,(hcor s hs j).2.2⟩) (t-1/28) (1/20)
      (by linarith [ht.1]) (hY (t-1/28) (by linarith [ht.1])) i
    norm_num at h
    simpa only [sub_add_cancel] using h
  intro i
  refine ⟨fun t ht => hfloor t ht i,?_⟩
  have hi : IntervalIntegrable (fun t => X t i 2) volume 3 4 :=
    (show ContinuousOn (fun t => X t i 2) (Icc (3:ℝ) 4) from fun t ht =>
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hX t (by linarith [ht.1])) i) 2).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have h := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/160:ℝ)) volume 3 4)
    hi (fun t ht => hfloor t ht i)
  norm_num at h
  exact h

end
end C4Assemblies
