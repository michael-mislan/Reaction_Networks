import proofs.RAF1519.Refinement.PulseMean
import proofs.RAF1519.Refinement.MaterialStop
import proofs.RAF1519.Refinement.StockPath

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 30000

def weightedNodeCount {n : ℕ} (w : Fin 7 → ℝ) (N : MolecularState n) (i : Fin n) : ℝ :=
  ∑ s, w s*(N (i,s):ℝ)

theorem weightedNodeCount_normalized {n : ℕ} (w : Fin 7 → ℝ) (V : ℝ)
    (N : MolecularState n) (i : Fin n) :
    weightedNodeCount w N i/V=weightedCoordinate w (concentration V (fun s => N (i,s))) := by
  simp only [weightedNodeCount,weightedCoordinate,concentration,Finset.sum_div,mul_div_assoc]

theorem pulse_materialWeight_bounds (b : Bool) (s : Fin 7) :
    0 ≤ materialWeight b s ∧ materialWeight b s ≤ 2 := by
  cases b <;> fin_cases s <;> norm_num [materialWeight,weightA,weightB]

theorem pulse_stockWeight_bounds (s : Fin 7) :
    0 ≤ stockWeight s ∧ stockWeight s ≤ 2 ∧ stockWeight s ≤ weightA s := by
  fin_cases s <;> norm_num [stockWeight,weightA]

theorem ready_material_count {n : ℕ} (V : ℝ) (hV : 0 < V)
    (N : MolecularState n) (i : Fin n) (h : Ready (1/100) (concentration V (fun s => N (i,s))))
    (b : Bool) :
    (159/160)*V ≤ weightedNodeCount (materialWeight b) N i ∧
    weightedNodeCount (materialWeight b) N i ≤ (161/160)*V := by
  have hn : 159/160 ≤ weightedNodeCount (materialWeight b) N i/V ∧
      weightedNodeCount (materialWeight b) N i/V ≤ 161/160 := by
    rw [weightedNodeCount_normalized]
    cases b
    · simpa only [materialWeight,← materialA_weighted] using h.2.1
    · simpa only [materialWeight,← materialB_weighted] using h.2.2.1
  exact ⟨(le_div_iff₀ hV).mp hn.1,(div_le_iff₀ hV).mp hn.2⟩

theorem ready_stock_count {n : ℕ} (V : ℝ) (hV : 0 < V)
    (N : MolecularState n) (i : Fin n) (h : Ready (1/100) (concentration V (fun s => N (i,s)))) :
    V/20 ≤ weightedNodeCount stockWeight N i ∧ weightedNodeCount stockWeight N i ≤ (161/160)*V := by
  constructor
  · have hs := h.2.2.2.1
    rw [stock_weighted,← weightedNodeCount_normalized] at hs
    have hh := (le_div_iff₀ hV).mp hs
    linarith
  · apply le_trans _ (ready_material_count V hV N i h false).2
    apply Finset.sum_le_sum
    intro s _
    exact mul_le_mul_of_nonneg_right (pulse_stockWeight_bounds s).2.2 (Nat.cast_nonneg _)

end
end RAF1519.Refinement
