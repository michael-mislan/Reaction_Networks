import proofs.RAF1519.Refinement.GraphDriftBinding

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

theorem exchange_graph_compensator_sum {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0) (N : MolecularState n)
    (u : Fin n) (t : Fin 7) :
    (∑ a : Fin n × Fin n × Fin 7,
      molecularRate r d k V N (.inr a)*molecularIncrement r d k V (u,t) N (.inr a)) =
      (∑ j, k j u*((N (j,t):ℝ)/V))-(∑ j, k u j*((N (u,t):ℝ)/V)) := by
  simp_rw [Fintype.sum_prod_type,exchange_graph_compensator r d k V hV]
  simp only [mul_sub,Finset.sum_sub_distrib]
  simp [Prod.mk.injEq,ite_and,mul_ite,Finset.sum_ite_irrel]

/-- Exact generator of the literal unrestricted graph count law. -/
theorem molecular_drift_binding {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : V ≠ 0)
    (hsym : ∀ i j, k i j = k j i) (N : MolecularState n) (p : Fin n × Fin 7) :
    (∑ a, molecularRate r d k V N a*molecularIncrement r d k V p N a) =
      countDrift (r p.1) (d p.1) (1/100) (1/100) V
        (concentration V (fun s => N (p.1,s))) p.2 +
      ∑ j, k p.1 j*((N (j,p.2):ℝ)/V-(N p:ℝ)/V) := by
  rw [Fintype.sum_sum_type,local_graph_compensator_sum r d k V hV]
  rw [exchange_graph_compensator_sum r d k V hV N p.1 p.2]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym j p.1]
  ring

end
end RAF1519.Refinement
