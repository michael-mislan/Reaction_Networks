import proofs.C4Assemblies.OutputSupplies

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

structure AssemblyCycle (P : Parameters ι) (p : ι → Intervention) (c : Assembly ι) where
  trajectory : ℝ → Assembly ι
  initial : trajectory 0 = assemblyPulse p c
  nonnegative : ∀ t, 0 ≤ t → ∀ i, Nonneg (trajectory t i)
  derivative : ∀ t, 0 ≤ t → HasDerivAt trajectory (assemblyField P.k P.r P.d (trajectory t)) t
  recovered : AssemblyReady (trajectory 3)
  terminal : AssemblyReady (trajectory 4)
  output : ∀ i, 1/28 ≤ routineExport (fun t => trajectory t i)
  free_floor : ∀ i, ∀ t ∈ Set.Icc (3:ℝ) 4, 1/540 ≤ trajectory t i 2
  free_output : ∀ i, 1/540 ≤ ∫ t in (3:ℝ)..4, trajectory t i 2
  foodU : ∀ i, routineFoodU (p i) ≤ 951/200
  foodW : ∀ i, routineFoodW (p i) ≤ 951/200
  service : ∀ i, routineService (P.d i) (fun t => trajectory t i) ≤ 9/50

def chooseAssemblyCycle (P : Parameters ι) (p : ι → Intervention)
    (c : Assembly ι) (hc : AssemblyReady c) : AssemblyCycle P p c := by
  let he := exists_assembly_routine P p c hc
  let X := Classical.choose he
  obtain ⟨h0,hn,hX,h3,h4⟩ := Classical.choose_spec he
  have ho := assembly_routine_output_supplies P p c hc X h0 hn hX
  have hf := assembly_routine_free_export P p c hc X h0 hn hX
  exact ⟨X,h0,hn,hX,h3,h4,fun i => (ho i).1,fun i => (hf i).1,
    fun i => (hf i).2,fun i => (ho i).2.1,fun i => (ho i).2.2.1,
    fun i => (ho i).2.2.2⟩

/-- Only the completed [0,4] segment is exposed to the next intervention. -/
def completedSegment (X : ℝ → Assembly ι) : ℝ → Assembly ι := fun t => X (min 4 (max 0 t))
abbrev History (ι : Type*) := List (ℝ → Assembly ι)
abbrev Protocol (ι : Type*) := ℕ → History ι → Assembly ι → ι → Intervention

structure HistoryState (ι : Type*) where
  state : Assembly ι
  ready : AssemblyReady state
  history : History ι

def routineHistory (P : Parameters ι) (protocol : Protocol ι) (c : Assembly ι)
    (hc : AssemblyReady c) : ℕ → HistoryState ι
  | 0 => ⟨c,hc,[]⟩
  | n+1 =>
    let s := routineHistory P protocol c hc n
    let q := chooseAssemblyCycle P (protocol n s.history s.state) s.state s.ready
    ⟨q.trajectory 4,q.terminal,completedSegment q.trajectory :: s.history⟩

theorem arbitrary_assembly_operation (P : Parameters ι) (protocol : Protocol ι)
    (c : Assembly ι) (hc : AssemblyReady c) :
    ∃ s : ℕ → Assembly ι, ∃ X : ℕ → ℝ → Assembly ι, ∃ H : ℕ → History ι,
      s 0 = c ∧ H 0 = [] ∧ (∀ n, AssemblyReady (s n)) ∧
      (∀ n, X n 0 = assemblyPulse (protocol n (H n) (s n)) (s n) ∧
        X n 4 = s (n+1) ∧ H (n+1) = completedSegment (X n) :: H n ∧
        (∀ t, 0 ≤ t → ∀ i, Nonneg (X n t i)) ∧
        (∀ t, 0 ≤ t → HasDerivAt (X n) (assemblyField P.k P.r P.d (X n t)) t) ∧
        AssemblyReady (X n 3) ∧ AssemblyReady (X n 4) ∧
        (∀ i, ∀ t ∈ Set.Icc (3:ℝ) 4, 1/540 ≤ X n t i 2)) ∧
      (∀ m : ℕ, ∀ i,
        (m:ℝ)/28 ≤ ∑ n ∈ Finset.range m, routineExport (fun t => X n t i) ∧
        (m:ℝ)/540 ≤ ∑ n ∈ Finset.range m, ∫ t in (3:ℝ)..4, X n t i 2 ∧
        (∑ n ∈ Finset.range m, routineFoodU (protocol n (H n) (s n) i)) ≤ 951*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, routineFoodW (protocol n (H n) (s n) i)) ≤ 951*(m:ℝ)/200 ∧
        (∑ n ∈ Finset.range m, routineService (P.d i) (fun t => X n t i)) ≤ 9*(m:ℝ)/50) := by
  let s := routineHistory P protocol c hc
  let q := fun n => chooseAssemblyCycle P (protocol n (s n).history (s n).state) (s n).state (s n).ready
  refine ⟨fun n => (s n).state,fun n => (q n).trajectory,fun n => (s n).history,
    rfl,rfl,fun n => (s n).ready,?_,?_⟩
  · intro n
    exact ⟨(q n).initial,rfl,rfl,(q n).nonnegative,(q n).derivative,
      (q n).recovered,(q n).terminal,(q n).free_floor⟩
  · intro m i
    have ho := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).output i)
    have hx := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).free_output i)
    have hu := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).foodU i)
    have hw := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).foodW i)
    have hg := Finset.sum_le_sum (s := Finset.range m) (fun n _ => (q n).service i)
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at ho hx hu hw hg
    exact ⟨by convert ho using 1; ring,by convert hx using 1; ring,
      by convert hu using 1; ring,by convert hw using 1; ring,by convert hg using 1; ring⟩

end
end C4Assemblies
