import proofs.C4Assemblies.Publication
import proofs.C4Assemblies.FineFreeProduct

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem fine_conservative_assembly_operation (P : Parameters ι) (p0 : ι → Intervention)
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
        (∀ i, ∀ t ∈ Set.Icc (3:ℝ) 4, 1/160 ≤ X n t i 2)) ∧
      (∀ m : ℕ,
        (Fintype.card ι : ℝ)*(m:ℝ)/28 ≤
          ∑ i, ∑ n ∈ Finset.range m, routineExport (fun t => X n t i) ∧
        (Fintype.card ι : ℝ)*(m:ℝ)/160 ≤
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
  obtain ⟨C,s,X,H,hC0,hCn,hC,hs0,hH0,hs,hcycle,hsums⟩ :=
    conservative_assembly_operation P p0 protocol c hc
  have hf (n : ℕ) := fine_assembly_routine_free_export P
    (protocol n (H n) (s n)) (s n) (hs n) (X n) (hcycle n).1
    (hcycle n).2.2.2.1 (hcycle n).2.2.2.2.1
  refine ⟨C,s,X,H,hC0,hCn,hC,hs0,hH0,hs,?_,?_⟩
  · intro n
    exact ⟨(hcycle n).1,(hcycle n).2.1,(hcycle n).2.2.1,
      (hcycle n).2.2.2.1,(hcycle n).2.2.2.2.1,
      (hcycle n).2.2.2.2.2.1,(hcycle n).2.2.2.2.2.2.1,fun i => (hf n i).1⟩
  · intro m
    have hx := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.range m) (fun n _ => (hf n i).2))
    simp only [Finset.sum_const,Finset.card_univ,Finset.card_range,nsmul_eq_mul] at hx
    refine ⟨(hsums m).1,?_,(hsums m).2.2⟩
    convert hx using 1
    ring

def fine_path_operation := fine_conservative_assembly_operation pathParameters
  (fun _ => fixedPulse) (fun _ _ _ _ => fixedPulse) heterogeneousReady
  (fun i => strong_admitted _ (heterogeneous_ready i))

def fine_ring_operation := fine_conservative_assembly_operation ringParameters
  (fun _ => fixedPulse) (fun _ _ _ _ => fixedPulse) heterogeneousReady
  (fun i => strong_admitted _ (heterogeneous_ready i))

end
end C4Assemblies
