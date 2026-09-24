import proofs.RAF1519.Refinement.PulseCountMaterial
import proofs.RAF1519.Refinement.PulseDistribution
import proofs.RAF1519.Refinement.CategoricalEvent

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 40000

def pulseSign (positive : Bool) : ℝ := if positive then 1 else -1

def pulseMaterialBad {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention)
    (i : Fin n) (b sign : Bool) : Set (PulseOutcomes N) :=
  {o | (V:ℝ)/100 ≤ pulseSign sign*(categoricalStock (pulseNodeWeight i (materialWeight b)) o-
    categoricalMean (graphPulseCategory N p) (pulseNodeWeight i (materialWeight b)))}

def pulseStockBad {n : ℕ} (N : MolecularState n) (V : ℕ) (p : Fin n → Intervention)
    (i : Fin n) : Set (PulseOutcomes N) :=
  {o | (V:ℝ)/4000 ≤ -(categoricalStock (pulseNodeWeight i stockWeight) o-
    categoricalMean (graphPulseCategory N p) (pulseNodeWeight i stockWeight))}

theorem pulseMaterialBad_probability {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 0 < (V:ℝ))
    (p : Fin n → Intervention) (i : Fin n)
    (hready : Ready (1/100) (concentration V (fun s => N (i,s)))) (b sign : Bool) :
    categoricalProbability (graphPulseCategory N p) (pulseMaterialBad N V p i b sign) ≤
      Real.exp (-(V:ℝ)/100000) := by
  have hbound : (∑ m : PulseMolecules N, pulseNodeWeight i (materialWeight b) m) ≤ (161/160)*(V:ℝ) := by
    rw [pulseNodeWeight_total]
    exact (ready_material_count V hV N i hready b).2
  have hs : |pulseSign sign|=1 := by cases sign <;> norm_num [pulseSign]
  exact categorical_material_tail (graphPulseCategory N p) (graphPulseCategory_nonnegative N p)
    (graphPulseCategory_total N p) (pulseNodeWeight i (materialWeight b))
    (fun m => (pulseNodeWeight_bounds N i (materialWeight b) (pulse_materialWeight_bounds b) m).1)
    (fun m => (pulseNodeWeight_bounds N i (materialWeight b) (pulse_materialWeight_bounds b) m).2)
    V (pulseSign sign) hV.le hs hbound

theorem pulseStockBad_probability {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 0 < (V:ℝ))
    (p : Fin n → Intervention) (i : Fin n)
    (hready : Ready (1/100) (concentration V (fun s => N (i,s)))) :
    categoricalProbability (graphPulseCategory N p) (pulseStockBad N V p i) ≤
      Real.exp (-(V:ℝ)/100000000) := by
  have hbound : (∑ m : PulseMolecules N, pulseNodeWeight i stockWeight m) ≤ (161/160)*(V:ℝ) := by
    rw [pulseNodeWeight_total]
    exact (ready_stock_count V hV N i hready).2
  have hb := categorical_stock_tail (graphPulseCategory N p) (graphPulseCategory_nonnegative N p)
    (graphPulseCategory_total N p) (pulseNodeWeight i stockWeight)
    (fun m => (pulseNodeWeight_bounds N i stockWeight (fun s => ⟨(pulse_stockWeight_bounds s).1,
      (pulse_stockWeight_bounds s).2.1⟩) m).1)
    (fun m => (pulseNodeWeight_bounds N i stockWeight (fun s => ⟨(pulse_stockWeight_bounds s).1,
      (pulse_stockWeight_bounds s).2.1⟩) m).2)
    V hV.le hbound
  simpa only [categoricalProbability,pulseStockBad,categoricalTail,neg_one_mul,Set.mem_setOf_eq] using hb

end
end RAF1519.Refinement
