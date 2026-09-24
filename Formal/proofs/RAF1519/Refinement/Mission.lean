import proofs.RAF1519.Refinement.ConnectedInstance

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopyReactor
open scoped ENNReal BigOperators

/-- Exact fixed-parameter mission theorem, including arbitrary continuous history
observations whenever their admissible transition obeys the literal conditional law. -/
theorem R15_S {H : Type*} [MeasurableSpace H] {n : ℕ}
    (hn : 0 < n) (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℕ)
    (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (R : PhysicalHistory H hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)))
    (m : ℕ) (h : H) (hlog : R.log h = [])
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => R.current h (i,s)))) :
    ENNReal.ofReal (max 0 (1-29*n*m*Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3)))) ≤
      fullHistoryKernel R.step m h (historyMission R) := by
  have he : 1-(m:ℝ)*cycleError n V Δ =
      1-29*n*m*Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3)) := by unfold cycleError; ring
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal
      (1-29*n*m*Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))) from bot_le), ← he]
  exact R15_S_history hn r d k V hV Δ hΔ hr hd hk hsym hdegree R m h hlog hready

/-- Concrete normalized unrestricted law for every controller on the complete
history of returned states and physical marked outputs. -/
theorem returned_mission {n : ℕ}
    (hn : 0 < n) (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℕ)
    (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (N : MolecularState n) (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s))))
    (policy : ReturnedHistory n → Fin n → Intervention) (m : ℕ) :
    let R := returnedPhysicalHistory hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N policy
    ENNReal.ofReal (1-(m:ℝ)*cycleError n V Δ) ≤ fullHistoryKernel R.step m [] (historyMission R) := by
  dsimp only
  exact R15_S_history hn r d k V hV Δ hΔ hr hd hk hsym hdegree _ m [] rfl hready

theorem connected_hundred_cycle_mission
    (r d : Fin 2 → ℝ) (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21)
    (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (policy : ReturnedHistory 2 → Fin 2 → Intervention) :
    let R := returnedPhysicalHistory (by norm_num : 0 < 2) r d exampleExchange exampleVolume
      (fun i => le_trans (by norm_num) (hr i).1) (fun i => le_trans (by norm_num) (hd i).1)
      exampleExchange_nonneg (by norm_num [exampleVolume]) exampleCounts policy
    ENNReal.ofReal (99/100) < fullHistoryKernel R.step 100 [] (historyMission R) := by
  dsimp only
  have hl := returned_mission (by norm_num : 0 < 2) r d exampleExchange exampleVolume
    (by norm_num [exampleVolume]) 1 (by norm_num) hr hd exampleExchange_nonneg
    exampleExchange_symmetric exampleExchange_degree exampleCounts exampleCounts_ready policy 100
  have hb := ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (q := 1-100*cycleError 2 exampleVolume 1) (by norm_num : (0:ℝ) ≤ 99/100)
  exact (hb.mpr connected_mission_bound).trans_le hl

#print axioms R15_S
#print axioms returned_mission
#print axioms connected_hundred_cycle_mission
end
end RAF1519.Refinement
