import proofs.RAF1519.Refinement.CountDriftBinding
import proofs.RAF1519.Refinement.CountJumps

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

theorem molecular_compensator_stoichiometry {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (N : MolecularState n)
    (a : CountChannel n) (p : Fin n × Fin 7) :
    molecularRate r d k V N a*molecularIncrement r d k V p N a =
      molecularRate r d k V N a*
        (((graphReaction r d k a).produce p:ℝ)-((graphReaction r d k a).consume p:ℝ))/V := by
  unfold molecularIncrement molecularNext molecularRate
  rw [← mul_div_assoc,Reaction.rate_increment]

theorem local_graph_compensator {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (N : MolecularState n)
    (i : Fin n) (a : LocalChannel) (p : Fin n × Fin 7) :
    molecularRate r d k V N (.inl (i,a))*molecularIncrement r d k V p N (.inl (i,a)) =
      if i=p.1 then localCompensator (r i) (d i) V (fun s => N (i,s)) a p.2 else 0 := by
  by_cases hi : i=p.1
  · rw [if_pos hi,molecular_compensator_stoichiometry,local_compensator_stoichiometry]
    change (atNode i (localReaction (r i) (d i) a)).rate V N * _ / V = _
    rw [atNode_rate]
    simp [graphReaction,atNode,hi]
  · rw [if_neg hi,local_increment_off_node r d k V N p i a (Ne.symm hi),mul_zero]

theorem local_graph_compensator_sum {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0) (N : MolecularState n)
    (p : Fin n × Fin 7) :
    (∑ a : Fin n × LocalChannel,
      molecularRate r d k V N (.inl a)*molecularIncrement r d k V p N (.inl a)) =
      countDrift (r p.1) (d p.1) (1/100) (1/100) V
        (concentration V (fun s => N (p.1,s))) p.2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [local_graph_compensator]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact local_compensator_sum (r p.1) (d p.1) V hV _ p.2

theorem exchange_graph_compensator {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0) (N : MolecularState n)
    (i j : Fin n) (s : Fin 7) (p : Fin n × Fin 7) :
    molecularRate r d k V N (.inr (i,j,s))*molecularIncrement r d k V p N (.inr (i,j,s)) =
      k i j*((N (i,s):ℝ)/V)*((if p=(j,s) then 1 else 0)-(if p=(i,s) then 1 else 0)) := by
  rw [molecular_compensator_stoichiometry,exchange_rate r d k V hV]
  simp only [graphReaction,Pi.single_apply]
  split_ifs <;> norm_num <;> ring

end
end RAF1519.Refinement
