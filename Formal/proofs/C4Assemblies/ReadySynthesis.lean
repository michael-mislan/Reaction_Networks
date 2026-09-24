import proofs.C4Assemblies.Synthesis
import proofs.C4Assemblies.SupplyCeiling

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem ready_mission_synthesis (P : Parameters ι)
    (p : ℕ → ι → Intervention) (c : Assembly ι) (hc : AssemblyReady c)
    (s : ℕ → Assembly ι) (X : ℕ → ℝ → Assembly ι)
    (hs0 : s 0 = c)
    (h0 : ∀ n, X n 0 = assemblyPulse (p n) (s n))
    (h4 : ∀ n, X n 4 = s (n+1))
    (hn : ∀ n t, 0 ≤ t → ∀ i, Nonneg (X n t i))
    (hX : ∀ n t, 0 ≤ t → HasDerivAt (X n) (assemblyField P.k P.r P.d (X n t)) t) :
    ∀ m : ℕ, (Fintype.card ι : ℝ)*(((m:ℝ)+1)/28-161/160) ≤
      ∑ n ∈ Finset.range m, assemblyNet P.r P.d 4 (X n) := by
  have hready : ∀ n, AssemblyReady (s n) := by
    intro n
    induction n with
    | zero =>
      rw [hs0]
      exact hc
    | succ n ih =>
      rw [← h4 n]
      exact (assembly_routine_return P (p n) (s n) ih (X n) (h0 n) (hn n) (hX n)).2 4 (by norm_num)
  have hnet (n : ℕ) : totalInventory (s (n+1))-totalInventory (s n)+assemblyExport (X n) ≤
      assemblyNet P.r P.d 4 (X n) := by
    have h := assembly_routine_net_lower P (p n) (s n) (fun i => (hready n i).1)
      (X n) (h0 n) (hn n) (hX n)
    rw [h4 n] at h
    exact h
  have hupper : totalInventory c ≤ (Fintype.card ι : ℝ)*(161/160) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (inventory_le_material (c i) (hc i).1).1.trans (hc i).2.1.2)
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

end
end C4Assemblies
