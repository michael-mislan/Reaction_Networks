import proofs.RAF1519.Refinement.CategoricalPulse
import proofs.RAF1519.Refinement.CountLaw
import proofs.RAF1519.Refinement.PulseCategories

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option maxHeartbeats 20000

abbrev PulseMolecules {n : ℕ} (N : MolecularState n) := (p : Fin n × Fin 7) × Fin (N p)
abbrev PulseOutcomes {n : ℕ} (N : MolecularState n) := PulseMolecules N → Fin 3

def graphPulseCategory {n : ℕ} (N : MolecularState n) (p : Fin n → Intervention) :
    PulseMolecules N → Fin 3 → ℝ := fun m => pulseCategory (p m.1.1) m.1.2

def pulseCategoryCounts {n : ℕ} (N : MolecularState n) (o : PulseOutcomes N) (a : Fin 3) : MolecularState n :=
  fun p => ∑ j : Fin (N p), if o ⟨p,j⟩=a then 1 else 0

theorem pulse_category_accounting {n : ℕ} (N : MolecularState n) (o : PulseOutcomes N) (p : Fin n × Fin 7) :
    (∑ a, pulseCategoryCounts N o a p)=N p := by
  unfold pulseCategoryCounts
  rw [Finset.sum_comm]
  have h (j : Fin (N p)) : (∑ a : Fin 3, if o ⟨p,j⟩=a then 1 else 0)=(1:ℕ) := by simp
  simp_rw [h]
  simp

theorem pulse_category_le {n : ℕ} (N : MolecularState n) (o : PulseOutcomes N)
    (a : Fin 3) (p : Fin n × Fin 7) : pulseCategoryCounts N o a p ≤ N p := by
  calc
    pulseCategoryCounts N o a p ≤ ∑ b : Fin 3, pulseCategoryCounts N o b p :=
      Finset.single_le_sum (fun b _ => Nat.zero_le (pulseCategoryCounts N o b p)) (Finset.mem_univ a)
    _ = N p := pulse_category_accounting N o p

def pulseDose (V : ℕ) (p : Intervention) (food : Fin 2) : ℕ :=
  ⌊(V:ℝ)*(1-p.q+(if food=0 then p.eU else p.eW))⌋₊

def postPulseState {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention)
    (o : PulseOutcomes N) : MolecularState n :=
  fun q => pulseCategoryCounts N o 0 q+
    if q.2=0 then pulseDose V (p q.1) 0 else if q.2=1 then pulseDose V (p q.1) 1 else 0

theorem postPulse_intermediate_le {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention)
    (o : PulseOutcomes N) (i : Fin n) : postPulseState N V p o (i,6) ≤ N (i,6) := by
  simpa only [postPulseState,show ¬(6:Fin 7)=0 by decide,show ¬(6:Fin 7)=1 by decide,
    if_false,Nat.add_zero] using pulse_category_le N o 0 (i,6)

end
end RAF1519.Refinement
