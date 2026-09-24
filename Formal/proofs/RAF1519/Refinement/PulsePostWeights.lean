import proofs.RAF1519.Refinement.PulseCountMaterial
import proofs.RAF1519.Refinement.PulseRefill

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 30000

theorem postPulse_weighted {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention)
    (o : PulseOutcomes N) (i : Fin n) (w : Fin 7 → ℝ) :
    weightedNodeCount w (postPulseState N V p o) i =
      categoricalStock (pulseNodeWeight i w) o+
      w 0*(pulseDose V (p i) 0:ℝ)+w 1*(pulseDose V (p i) 1:ℝ) := by
  rw [pulseNodeWeight_retained]
  unfold weightedNodeCount postPulseState
  simp only [Nat.cast_add,mul_add,Finset.sum_add_distrib]
  have he : (∑ s : Fin 7, w s*((if s=0 then pulseDose V (p i) 0 else
      if s=1 then pulseDose V (p i) 1 else 0 : ℕ):ℝ)) =
      w 0*(pulseDose V (p i) 0:ℝ)+w 1*(pulseDose V (p i) 1:ℝ) := by
    have hp : ∀ s : Fin 7,
        w s*((if s=0 then pulseDose V (p i) 0 else if s=1 then pulseDose V (p i) 1 else 0 : ℕ):ℝ) =
        (if s=0 then w 0*(pulseDose V (p i) 0:ℝ) else 0)+
        (if s=1 then w 1*(pulseDose V (p i) 1:ℝ) else 0) := by
      intro s
      by_cases h0 : s=0
      · subst s
        norm_num
      · by_cases h1 : s=1
        · subst s
          norm_num
        · simp only [if_neg h0,if_neg h1,Nat.cast_zero,mul_zero,zero_add]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [he]
  ring

def materialFood (b : Bool) : Fin 2 := if b then 1 else 0

theorem postPulse_material {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention)
    (o : PulseOutcomes N) (i : Fin n) (b : Bool) :
    weightedNodeCount (materialWeight b) (postPulseState N V p o) i =
      categoricalStock (pulseNodeWeight i (materialWeight b)) o+(pulseDose V (p i) (materialFood b):ℝ) := by
  rw [postPulse_weighted]
  cases b <;> norm_num [materialWeight,weightA,weightB,materialFood]

theorem postPulse_stock {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention)
    (o : PulseOutcomes N) (i : Fin n) :
    weightedNodeCount stockWeight (postPulseState N V p o) i =
      categoricalStock (pulseNodeWeight i stockWeight) o := by
  rw [postPulse_weighted]
  norm_num [stockWeight]

end
end RAF1519.Refinement
