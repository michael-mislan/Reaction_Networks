import proofs.C4Assemblies.Repeated
import proofs.C4Assemblies.SharedAccounts
import proofs.C4Assemblies.LiteralSource
import proofs.C4Assemblies.Uniqueness
import proofs.C4Assemblies.Inventory

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- Actual conservative assembly operation. No successful-operation premise is supplied. -/
theorem conservative_assembly_operation (P : Parameters ι) (p0 : ι → Intervention)
    (protocol : Protocol ι) (c : Assembly ι) (hc : AssemblyAdmitted c) :
    ∃ C : ℝ → Assembly ι, ∃ s : ℕ → Assembly ι,
    ∃ X : ℕ → ℝ → Assembly ι, ∃ H : ℕ → History ι,
      C 0 = assemblyPulse p0 c ∧
      (∀ t, 0 ≤ t → ∀ i, Nonneg (C t i)) ∧
      (∀ t, 0 ≤ t → HasDerivAt C (assemblyField P.k P.r P.d (C t)) t) ∧
      s 0 = C 12 ∧ H 0 = [] ∧ (∀ n, AssemblyReady (s n)) ∧
      (∀ n, X n 0 = assemblyPulse (protocol n (H n) (s n)) (s n) ∧
        X n 4 = s (n+1) ∧ H (n+1) = completedSegment (X n) :: H n ∧
        (∀ t, 0 ≤ t → ∀ i, Nonneg (X n t i)) ∧
        (∀ t, 0 ≤ t → HasDerivAt (X n) (assemblyField P.k P.r P.d (X n t)) t) ∧
        AssemblyReady (X n 3) ∧ AssemblyReady (X n 4) ∧
        (∀ i, ∀ t ∈ Set.Icc (3:ℝ) 4, 1/540 ≤ X n t i 2)) ∧
      (∀ m : ℕ,
        (Fintype.card ι : ℝ)*(m:ℝ)/28 ≤
          ∑ i, ∑ n ∈ Finset.range m, routineExport (fun t => X n t i) ∧
        (Fintype.card ι : ℝ)*(m:ℝ)/540 ≤
          ∑ i, ∑ n ∈ Finset.range m, ∫ t in (3:ℝ)..4, X n t i 2 ∧
        (∑ i, (12+(1-(p0 i).q+(p0 i).eU)+
          ∑ n ∈ Finset.range m, routineFoodU (protocol n (H n) (s n) i))) ≤
            (Fintype.card ι : ℝ)*(2551+951*(m:ℝ))/200 ∧
        (∑ i, (12+(1-(p0 i).q+(p0 i).eW)+
          ∑ n ∈ Finset.range m, routineFoodW (protocol n (H n) (s n) i))) ≤
            (Fintype.card ι : ℝ)*(2551+951*(m:ℝ))/200 ∧
        (∑ i, ((∫ t in (0:ℝ)..12, P.d i*C t i 2+P.d i*(1/8000000000)*C t i 0*C t i 1)+
          ∑ n ∈ Finset.range m, routineService (P.d i) (fun t => X n t i))) ≤
            (Fintype.card ι : ℝ)*(27+9*(m:ℝ))/50) := by
  obtain ⟨C,hC0,hCn,hC,hready⟩ := exists_assembly_conditioning P p0 c hc
  obtain ⟨s,X,H,hs0,hH0,hs,hcycle,hsums⟩ := arbitrary_assembly_operation P protocol (C 12) hready
  have hcond := assembly_conditioning_supplies P p0 c hc C hC0 hCn hC
  refine ⟨C,s,X,H,hC0,hCn,hC,hs0,hH0,hs,hcycle,?_⟩
  intro m
  have ho := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hsums m i).1)
  have hx := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hsums m i).2.1)
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    add_le_add (hcond i).1 (hsums m i).2.2.1)
  have hw := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    add_le_add (hcond i).2.1 (hsums m i).2.2.2.1)
  have hg := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    add_le_add (hcond i).2.2 (hsums m i).2.2.2.2)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ho hx hu hw hg
  exact ⟨by convert ho using 1; ring,by convert hx using 1; ring,
    by convert hu using 1; ring,by convert hw using 1; ring,by convert hg using 1; ring⟩

end
end C4Assemblies
