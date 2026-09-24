import proofs.RAF1519.Refinement.CountMass
import proofs.CompositionalMemory.JumpNonexplosion

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability Filter
open scoped BigOperators Topology

theorem molecular_mass_one_le {n : ℕ} (N : MolecularState n) : 1 ≤ molecularMass N := by
  unfold molecularMass Reaction.material
  have h := Finset.sum_nonneg (s := Finset.univ) (fun p _ =>
    mul_nonneg (le_trans (by norm_num) (mass_weight_positive p.2)) (Nat.cast_nonneg (N p)))
  linarith

theorem molecular_coordinate_le_mass {n : ℕ} (N : MolecularState n) (p : Fin n × Fin 7) :
    (N p:ℝ) ≤ molecularMass N := by
  have hsum := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => mul_nonneg (le_trans (by norm_num) (mass_weight_positive j.2)) (Nat.cast_nonneg (N j)))
    (Finset.mem_univ p)
  have hw := mul_nonneg (sub_nonneg.mpr (mass_weight_positive p.2)) (Nat.cast_nonneg (N p))
  unfold molecularMass Reaction.material
  nlinarith

theorem molecular_sublevel_finite {n : ℕ} (B : ℕ) :
    Set.Finite {N : MolecularState n | molecularMass N ≤ B} := by
  apply (Set.finite_Iic (fun _ : Fin n × Fin 7 => B)).subset
  intro N hN p
  have hp := (molecular_coordinate_le_mass N p).trans hN
  exact_mod_cast hp

theorem molecular_rates_locally_bounded {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (B : ℕ) :
    ∃ q : ℝ, 0 < q ∧ ∀ N : MolecularState n, molecularMass N ≤ B →
      (∑ a, molecularRate r d k V N a) ≤ q := by
  obtain ⟨q,hq⟩ := ((molecular_sublevel_finite (n := n) B).image
    (fun N => ∑ a, molecularRate r d k V N a)).bddAbove
  refine ⟨max q 1,lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _),?_⟩
  intro N hN
  exact (hq ⟨N,hN,rfl⟩).trans (le_max_left _ _)

/-- The unrestricted marked law has no finite accumulation of reaction times. -/
theorem molecular_nonexplosive {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (N : MolecularState n) :
    ∀ᵐ z ∂molecularLaw hn r d k V hr hd hk hV N,
      Tendsto (waitingSum (fun i => (z (i+1)).2.2)) atTop atTop := by
  apply CompositionalMemory.jump_times_diverge N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr hd hk hV.le)
    (molecular_total_positive hn r d k V hr hd hk hV)
    molecularMass molecular_mass_positive (2*n*V) (by positivity)
  · intro x
    exact (molecular_generator_bound r d k V hr hd hk hV.le x).trans
      (le_mul_of_one_le_right (by positivity) (molecular_mass_one_le x))
  · exact molecular_rates_locally_bounded r d k V

#print axioms molecular_nonexplosive

end
end RAF1519.Refinement
