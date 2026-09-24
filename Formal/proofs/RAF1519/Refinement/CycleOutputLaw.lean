import proofs.RAF1519.Refinement.CycleOutput

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal BigOperators

def cycleError (n V : ℕ) (Δ : ℝ) : ℝ :=
  29*n*Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))

theorem cycleError_nonneg (n V : ℕ) (Δ : ℝ) : 0 ≤ cycleError n V Δ := by
  unfold cycleError
  positivity

theorem literalCycle_failure {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    literalCycleLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N p
      {X | ¬cycleOutputSuccess V X} ≤ ENNReal.ofReal (cycleError n V Δ) := by
  rw [literalCycleLaw, Measure.map_apply (cycleOutput_measurable V p)
    (Set.to_countable {X : CycleOutput n | ¬cycleOutputSuccess V X}).measurableSet]
  have he : ENNReal.ofReal (cycleError n V Δ) =
      29*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))) := by
    simp [cycleError, ENNReal.ofReal_mul]
  rw [he]
  exact pulseFlow_integer_failure hn r d k V hV Δ hΔ hr hd hk hsym hdegree N p hready

theorem literalCycle_success {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    ENNReal.ofReal (1-cycleError n V Δ) ≤
    literalCycleLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N p
      {X | cycleOutputSuccess V X} := by
  have hf := literalCycle_failure hn r d k V hV Δ hΔ hr hd hk hsym hdegree N p hready
  rw [ENNReal.ofReal_sub _ (cycleError_nonneg n V Δ), ENNReal.ofReal_one]
  apply tsub_le_iff_right.mpr
  have he := measure_add_measure_compl
    (μ := literalCycleLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N p)
    (Set.to_countable {X : CycleOutput n | cycleOutputSuccess V X}).measurableSet
  rw [measure_univ] at he
  rw [← he]
  exact add_le_add le_rfl hf

end
end RAF1519.Refinement
