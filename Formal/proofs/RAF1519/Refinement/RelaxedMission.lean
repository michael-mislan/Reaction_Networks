import proofs.RAF1519.Refinement.RelaxedProbability
import proofs.RAF1519.Refinement.Mission

namespace RAF1519.Refinement.Relaxed
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopyReactor Filter
open scoped BigOperators ENNReal
set_option maxHeartbeats 50000

def cycleError (n V : ℕ) (Δ : ℝ) : ℝ :=
  29*n*Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))

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
      29*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))) := by
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

theorem historyMission_step {H : Type*} [MeasurableSpace H] {n : ℕ}
    (hn : 0 < n) (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℕ)
    (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (R : PhysicalHistory H hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)))
    (h : H) (hh : h ∈ historyMission R) :
    ENNReal.ofReal (1-cycleError n V Δ) ≤ R.step h (historyMission R) := by
  have hp := literalCycle_success hn r d k V hV Δ hΔ hr hd hk hsym hdegree
    (R.current h) (R.policy h) hh.2
  rw [← R.conditional_law h, Measure.map_apply R.observe_measurable
    (Set.to_countable {X : CycleOutput n | cycleOutputSuccess V X}).measurableSet] at hp
  apply hp.trans (measure_mono_ae ?_)
  filter_upwards [R.log_extend h] with y hy
  intro hs
  constructor
  · rw [hy]
    intro X hX
    rcases List.mem_cons.mp hX with he | he
    · simpa only [he] using hs
    · exact hh.1 X he
  · rw [R.current_return y]
    exact fun i => (hs i).1

/-- Repeated mission bound on the unrestricted history probability law. -/

theorem R15_S_history {H : Type*} [MeasurableSpace H] {n : ℕ}
    (hn : 0 < n) (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℕ)
    (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (R : PhysicalHistory H hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)))
    (m : ℕ) (h : H) (hlog : R.log h = [])
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => R.current h (i,s)))) :
    ENNReal.ofReal (1-(m:ℝ)*cycleError n V Δ) ≤ fullHistoryKernel R.step m h (historyMission R) := by
  apply full_history_invariant_lower R.step (historyMission R) (historyMission_measurable R)
    (cycleError n V Δ) (cycleError_nonneg n V Δ)
    (historyMission_step hn r d k V hV Δ hΔ hr hd hk hsym hdegree R) m h
  exact ⟨by simp [hlog], hready⟩


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
    ENNReal.ofReal (max 0 (1-29*n*m*Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3)))) ≤
      fullHistoryKernel R.step m h (historyMission R) := by
  have he : 1-(m:ℝ)*cycleError n V Δ =
      1-29*n*m*Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3)) := by unfold cycleError; ring
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal
      (1-29*n*m*Real.exp (-(V:ℝ)/(2000000000000*(1+Δ)^3))) from bot_le), ← he]
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


#print axioms R15_S
end
end RAF1519.Refinement.Relaxed
