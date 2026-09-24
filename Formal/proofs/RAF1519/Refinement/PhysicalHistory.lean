import proofs.RAF1519.Refinement.CycleOutputLaw
import proofs.RAF1519.Refinement.HistoryInvariant

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopyReactor
open scoped ENNReal BigOperators

instance cycleLog_measurableSpace (n : ℕ) : MeasurableSpace (List (CycleOutput n)) := ⊤
instance cycleLog_measurableSingleton (n : ℕ) : MeasurableSingletonClass (List (CycleOutput n)) :=
  ⟨fun _ => trivial⟩

/-- H may contain arbitrary continuous observations. The conditional law is the
literal pulse and molecular flow; the log records every actual returned output. -/
structure PhysicalHistory (H : Type*) [MeasurableSpace H] {n : ℕ} (hn : 0 < n)
    (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℕ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i) (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) where
  current : H → MolecularState n
  observe : H → CycleOutput n
  observe_measurable : Measurable observe
  current_return : ∀ h, current h = (observe h).1
  log : H → List (CycleOutput n)
  log_measurable : Measurable log
  policy : H → (Fin n → Intervention)
  step : Kernel H H
  markov : IsMarkovKernel step
  conditional_law : ∀ h, (step h).map observe = literalCycleLaw hn r d k V hr hd hk hV (current h) (policy h)
  log_extend : ∀ h, ∀ᵐ y ∂step h, log y = observe y :: log h

def historyMission {H : Type*} [MeasurableSpace H] {n : ℕ} {hn r d k V hr hd hk hV}
    (R : PhysicalHistory H (n := n) hn r d k V hr hd hk hV) : Set H :=
  {h | (∀ X ∈ R.log h, cycleOutputSuccess V X) ∧
    ∀ i, Ready (1/100) (concentration V (fun s => R.current h (i,s)))}

theorem historyMission_measurable {H : Type*} [MeasurableSpace H] {n : ℕ} {hn r d k V hr hd hk hV}
    (R : PhysicalHistory H (n := n) hn r d k V hr hd hk hV) : MeasurableSet (historyMission R) := by
  have hlog := R.log_measurable ((Set.to_countable
    {L : List (CycleOutput n) | ∀ X ∈ L, cycleOutputSuccess V X}).measurableSet)
  have hready := R.observe_measurable ((Set.to_countable
    {X : CycleOutput n | ∀ i, Ready (1/100) (concentration V (fun s => X.1 (i,s)))}).measurableSet)
  simpa only [historyMission, R.current_return] using hlog.inter hready

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

#print axioms R15_S_history
end
end RAF1519.Refinement
