import proofs.RAF1519.Refinement.PulsePostWeights

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 40000

def CountPrepared {n : ℕ} (V : ℝ) (N : MolecularState n) : Prop :=
  (∀ b i, |materialNode b V N i-1| ≤ 1/25) ∧
  (∀ i, (N (i,6):ℝ)/V ≤ 1101/100000) ∧
  (∀ i, 12/1000 ≤ stock (concentration V (fun s => N (i,s))))

theorem postPulse_prepared {n : ℕ} (N : MolecularState n) (V : ℕ) (hV : 10000 ≤ V)
    (p : Fin n → Intervention) (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s))))
    (o : PulseOutcomes N)
    (hmat : ∀ b i, |categoricalStock (pulseNodeWeight i (materialWeight b)) o-
      categoricalMean (graphPulseCategory N p) (pulseNodeWeight i (materialWeight b))| < (V:ℝ)/100)
    (hstock : ∀ i, -(categoricalStock (pulseNodeWeight i stockWeight) o-
      categoricalMean (graphPulseCategory N p) (pulseNodeWeight i stockWeight)) < (V:ℝ)/4000) :
    CountPrepared V (postPulseState N V p o) := by
  have hVr : (10000:ℝ) ≤ V := by exact_mod_cast hV
  have hV0 : (0:ℝ) < V := by linarith
  refine ⟨?_,?_,?_⟩
  · intro b i
    have hmc := ready_material_count (V:ℝ) hV0 N i (hready i) b
    have hm := pulseNodeWeight_mean_bounds N p i (materialWeight b)
      (fun s => (pulse_materialWeight_bounds b s).1)
    let food := materialFood b
    let e := if food=0 then (p i).eU else (p i).eW
    have he : -(1/200) ≤ e ∧ e ≤ 1/200 := by
      dsimp only [e]
      split_ifs
      · exact ⟨(p i).eU_lower,(p i).eU_upper⟩
      · exact ⟨(p i).eW_lower,(p i).eW_upper⟩
    have hcenter := pulse_material_center_count V (p i).q e (weightedNodeCount (materialWeight b) N i)
      (categoricalMean (graphPulseCategory N p) (pulseNodeWeight i (materialWeight b))) hV0.le
      ⟨(p i).q_lower,(p i).q_upper⟩ he hmc hm
    have hh := pulse_material_prepared V _ _ _ _ hVr hcenter (pulseDose_rounding V (p i) food) (hmat b i)
    change |weightedCoordinate (materialWeight b) (concentration V (fun s => postPulseState N V p o (i,s)))-1| ≤ 1/25
    rw [← weightedNodeCount_normalized,postPulse_material]
    exact hh
  · intro i
    have hd := div_le_div_of_nonneg_right
      (show (postPulseState N V p o (i,6):ℝ) ≤ N (i,6) by exact_mod_cast postPulse_intermediate_le N V p o i) hV0.le
    have hr := (hready i).2.2.2.2
    change (N (i,6):ℝ)/(V:ℝ) ≤ (1101/1000)*(1/100) at hr
    linarith
  · intro i
    have hy := (ready_stock_count (V:ℝ) hV0 N i (hready i)).1
    have hm := (pulseNodeWeight_mean_bounds N p i stockWeight (fun s => (pulse_stockWeight_bounds s).1)).1
    have hl := pulse_stock_mean_lower V (p i).q (weightedNodeCount stockWeight N i) _ hV0.le
      (p i).q_lower hy hm
    have hh := pulse_stock_prepared V _ _ hV0 hl (hstock i)
    rw [stock_weighted,← weightedNodeCount_normalized,postPulse_stock]
    norm_num only at hh ⊢
    exact hh

end
end RAF1519.Refinement
