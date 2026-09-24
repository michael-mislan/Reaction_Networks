import proofs.RAF1519.Refinement.CountPulse

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 40000

theorem pulse_molecule_weight_sum {n : ℕ} (N : MolecularState n) (w : Fin n × Fin 7 → ℝ) :
    (∑ m : PulseMolecules N, w m.1)=∑ p, (N p:ℝ)*w p := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem pulse_retained_weight_sum {n : ℕ} (N : MolecularState n) (w : Fin n × Fin 7 → ℝ)
    (o : PulseOutcomes N) :
    categoricalStock (fun m : PulseMolecules N => w m.1) o =
      ∑ p, w p*(pulseCategoryCounts N o 0 p:ℝ) := by
  unfold categoricalStock
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp only [pulseCategoryCounts,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

def pulseNodeWeight {n : ℕ} {N : MolecularState n} (i : Fin n) (w : Fin 7 → ℝ)
    (m : PulseMolecules N) : ℝ := if m.1.1=i then w m.1.2 else 0

theorem node_weighted_sum {n : ℕ} (N : MolecularState n) (i : Fin n) (w : Fin 7 → ℝ) :
    (∑ p : Fin n × Fin 7, (if p.1=i then w p.2 else 0)*(N p:ℝ)) =
      ∑ s, w s*(N (i,s):ℝ) := by
  rw [Fintype.sum_prod_type]
  simp only [ite_mul,zero_mul]
  calc
    (∑ j : Fin n, ∑ s : Fin 7, if j=i then w s*(N (j,s):ℝ) else 0) =
        ∑ j : Fin n, if j=i then (∑ s : Fin 7, w s*(N (j,s):ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j=i <;> simp only [hj,if_true,if_false,Finset.sum_const_zero]
    _ = _ := by simp

theorem pulseNodeWeight_total {n : ℕ} (N : MolecularState n) (i : Fin n) (w : Fin 7 → ℝ) :
    (∑ m : PulseMolecules N, pulseNodeWeight i w m)=∑ s, w s*(N (i,s):ℝ) := by
  change (∑ m : PulseMolecules N, (if m.1.1=i then w m.1.2 else 0)) = _
  rw [pulse_molecule_weight_sum N (fun p => if p.1=i then w p.2 else 0)]
  rw [show (∑ p : Fin n × Fin 7, (N p:ℝ)*(if p.1=i then w p.2 else 0)) =
      ∑ p : Fin n × Fin 7, (if p.1=i then w p.2 else 0)*(N p:ℝ) from
        Finset.sum_congr rfl (fun p _ => mul_comm _ _)]
  exact node_weighted_sum N i w

theorem pulseNodeWeight_retained {n : ℕ} (N : MolecularState n) (i : Fin n) (w : Fin 7 → ℝ)
    (o : PulseOutcomes N) :
    categoricalStock (pulseNodeWeight i w) o = ∑ s, w s*(pulseCategoryCounts N o 0 (i,s):ℝ) := by
  unfold pulseNodeWeight
  rw [pulse_retained_weight_sum N (fun p => if p.1=i then w p.2 else 0) o]
  exact node_weighted_sum (pulseCategoryCounts N o 0) i w

theorem pulseNodeWeight_bounds {n : ℕ} (N : MolecularState n) (i : Fin n) (w : Fin 7 → ℝ)
    (hw : ∀ s, 0 ≤ w s ∧ w s ≤ 2) (m : PulseMolecules N) :
    0 ≤ pulseNodeWeight i w m ∧ pulseNodeWeight i w m ≤ 2 := by
  unfold pulseNodeWeight
  split_ifs
  · exact hw _
  · norm_num

end
end RAF1519.Refinement
