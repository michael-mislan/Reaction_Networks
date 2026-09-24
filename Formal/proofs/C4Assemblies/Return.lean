import proofs.C4Assemblies.Recovery

namespace C4Assemblies
noncomputable section
open ProductiveRecovery
variable {ι : Type*} [Fintype ι]

theorem assembly_conditioning_return (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    ∀ t, 12 ≤ t → AssemblyReady (X t) := by
  have hy0 : ∀ i, 49/1000000 ≤ Y (X 0 i) := by
    intro i
    rw [h0]
    have hp := pulse_catalyst (p i) (c i) (hc i).1
    change 49/1000000 ≤ Y (pulse (p i) (c i))
    linarith [(hc i).2.2.2]
  have he : (1/20:ℝ)/(49/1000000) ≤ Real.exp ((3/5)*12) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 36/5) 10
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have h := (assembly_trajectory_return P p c hc X h0 hn hX
    (49/1000000) 12 (by norm_num) hy0 (by norm_num) he).2
  norm_num at h
  exact h

theorem assembly_routine_return (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) (X : ℝ → Assembly ι)
    (h0 : X 0 = assemblyPulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, Nonneg (X t i))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) :
    (∀ t, 5/2 ≤ t → ∀ i, 1/20 ≤ Y (X t i)) ∧
    ∀ t, 3 ≤ t → AssemblyReady (X t) := by
  have hy0 : ∀ i, 49/4000 ≤ Y (X 0 i) := by
    intro i
    rw [h0]
    have hp := pulse_catalyst (p i) (c i) (hc i).1
    change 49/4000 ≤ Y (pulse (p i) (c i))
    linarith [(hc i).2.2.2]
  have he : (1/20:ℝ)/(49/4000) ≤ Real.exp ((3/5)*(5/2)) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have h := assembly_trajectory_return P p c (fun i => strong_admitted (c i) (hc i)) X h0 hn hX
    (49/4000) (5/2) (by norm_num) hy0 (by norm_num) he
  norm_num at h
  exact h

theorem exists_assembly_conditioning (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyAdmitted c) :
    ∃ X : ℝ → Assembly ι, X 0 = assemblyPulse p c ∧
      (∀ t, 0 ≤ t → ∀ i, Nonneg (X t i)) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) ∧
      AssemblyReady (X 12) := by
  obtain ⟨X,h0,hn,hX⟩ := assembly_global_nonnegative_solution P.k P.exchange_nonneg
    P.exchange_symmetric P.r P.d (fun i => by linarith [P.r_lower i])
    (fun i => by linarith [P.d_lower i]) (assemblyPulse p c)
    (fun i => pulse_nonnegative (p i) (c i) (hc i).1)
  exact ⟨X,h0,hn,hX,assembly_conditioning_return P p c hc X h0 hn hX 12 le_rfl⟩

theorem exists_assembly_routine (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) :
    ∃ X : ℝ → Assembly ι, X 0 = assemblyPulse p c ∧
      (∀ t, 0 ≤ t → ∀ i, Nonneg (X t i)) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (assemblyField P.k P.r P.d (X t)) t) ∧
      AssemblyReady (X 3) ∧ AssemblyReady (X 4) := by
  obtain ⟨X,h0,hn,hX⟩ := assembly_global_nonnegative_solution P.k P.exchange_nonneg
    P.exchange_symmetric P.r P.d (fun i => by linarith [P.r_lower i])
    (fun i => by linarith [P.d_lower i]) (assemblyPulse p c)
    (fun i => pulse_nonnegative (p i) (c i) (hc i).1)
  have hret := (assembly_routine_return P p c hc X h0 hn hX).2
  exact ⟨X,h0,hn,hX,hret 3 le_rfl,hret 4 (by norm_num)⟩

end
end C4Assemblies
