import proofs.SerialTransferSelection.RecoveryDock
import proofs.SerialTransferSelection.BatchDomain

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- A total readout, used for the restart only on the proved all-ready event.
The none branch remains a failure in the cycle law; it is never a replacement cell. -/
def recoveredCell (N : ℕ) (zL zH : ℝ) (tag : Bool)
    (c : {c : Compartment // c ∈ recoveryCellDomain N zL zH tag})
    (x : StoppedCompartment (recoveryCellDomain N zL zH tag)) : TaggedCell :=
  ⟨tag,(x.getD c).val⟩

theorem recoveredCell_ready (N : ℕ) (zL zH : ℝ) (tag : Bool)
    (c : {c : Compartment // c ∈ recoveryCellDomain N zL zH tag})
    (x : StoppedCompartment (recoveryCellDomain N zL zH tag))
    (hx : x ∈ readyRecoverySet N c.val.2 (recoveryCenter zL zH tag) (recoveryEnergy tag)) :
    (recoveredCell N zL zH tag c x).high=tag ∧
      (recoveredCell N zL zH tag c x).compartment.2=c.val.2 ∧
      cellEnergy zL zH (recoveredCell N zL zH tag c x) ≤ innerEnergy := by
  cases x with
  | none => exact False.elim hx
  | some d =>
    change d.val.2=c.val.2 ∧ _ ≤ innerEnergy at hx
    refine ⟨rfl,hx.1,?_⟩
    rw [← tagged_recovery_energy]
    exact hx.2

def recoveredRefill (M N : ℕ) (zL zH : ℝ) (tag : Fin M → Bool)
    (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)})
    (x : ∀ i, StoppedCompartment (recoveryCellDomain N zL zH (tag i))) : PopulationState :=
  preparePhaseBatch (List.ofFn (fun i => recoveredCell N zL zH (tag i) (c i) (x i)))

theorem recoveredRefill_ready (M N : ℕ) (zL zH : ℝ) (tag : Fin M → Bool)
    (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)})
    (hv : ∀ i, N ≤ (c i).val.2 ∧ (c i).val.2 < 2*N)
    (x : ∀ i, StoppedCompartment (recoveryCellDomain N zL zH (tag i)))
    (hx : ∀ i, x i ∈ readyRecoverySet N (c i).val.2
      (recoveryCenter zL zH (tag i)) (recoveryEnergy (tag i))) :
    PhaseReadyPopulation N M zL zH (recoveredRefill M N zL zH tag c x) := by
  refine ⟨by simp [recoveredRefill,preparePhaseBatch],rfl,rfl,?_,?_⟩
  · intro d hd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    have hi := (recoveredCell_ready N zL zH (tag i) (c i) (x i) (hx i)).2.1
    rw [hi]
    exact hv i
  · intro d hd
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    exact (recoveredCell_ready N zL zH (tag i) (c i) (x i) (hx i)).2.2

theorem ancestralCount_as_sum (tag : Bool) (cs : List TaggedCell) :
    ancestralCount tag cs = (cs.map (fun c => if c.high=tag then 1 else 0)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases ht : c.high=tag <;> simp [ancestralCount,ht] at ih ⊢ <;> omega

theorem recoveredRefill_ancestry (M N : ℕ) (zL zH : ℝ) (tag : Fin M → Bool)
    (c : ∀ i, {c : Compartment // c ∈ recoveryCellDomain N zL zH (tag i)})
    (x : ∀ i, StoppedCompartment (recoveryCellDomain N zL zH (tag i)))
    (hx : ∀ i, x i ∈ readyRecoverySet N (c i).val.2
      (recoveryCenter zL zH (tag i)) (recoveryEnergy (tag i))) (b : Bool) :
    let original := List.ofFn (fun i => (⟨tag i,(c i).val⟩ : TaggedCell))
    ancestralCount b (recoveredRefill M N zL zH tag c x).live=ancestralCount b original ∧
      ancestralMembrane b (recoveredRefill M N zL zH tag c x).live=ancestralMembrane b original := by
  constructor
  · simp only [ancestralCount_as_sum,recoveredRefill,preparePhaseBatch,List.map_ofFn,recoveredCell]
    rfl
  · simp only [ancestralMembrane,recoveredRefill,preparePhaseBatch,List.map_ofFn]
    congr 1
    apply congrArg List.ofFn
    funext i
    have hi := recoveredCell_ready N zL zH (tag i) (c i) (x i) (hx i)
    dsimp only [Function.comp_def]
    rw [hi.1,hi.2.1]

end SerialTransferSelection
