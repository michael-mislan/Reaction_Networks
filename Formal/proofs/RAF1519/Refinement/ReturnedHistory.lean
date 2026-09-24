import proofs.RAF1519.Refinement.PhysicalHistory

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopyReactor
open scoped ENNReal BigOperators

abbrev ReturnedHistory (n : ℕ) := List (CycleOutput n)

def returnedObservation {n : ℕ} (N : MolecularState n) (h : ReturnedHistory n) : CycleOutput n :=
  h.headD (N, fun _ _ => 0)

def returnedHistoryStep {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n)
    (policy : ReturnedHistory n → Fin n → Intervention) : Kernel (ReturnedHistory n) (ReturnedHistory n) :=
  Kernel.ofFunOfCountable (fun h =>
    (literalCycleLaw hn r d k V hr hd hk hV (returnedObservation N h).1 (policy h)).map (fun X => X::h))

instance returnedHistoryStep_markov {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n)
    (policy : ReturnedHistory n → Fin n → Intervention) :
    IsMarkovKernel (returnedHistoryStep hn r d k V hr hd hk hV N policy) := by
  constructor
  intro h
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

def returnedPhysicalHistory {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n)
    (policy : ReturnedHistory n → Fin n → Intervention) :
    PhysicalHistory (ReturnedHistory n) hn r d k V hr hd hk hV where
  current h := (returnedObservation N h).1
  observe := returnedObservation N
  observe_measurable := measurable_of_countable _
  current_return _ := rfl
  log := id
  log_measurable := measurable_id
  policy := policy
  step := returnedHistoryStep hn r d k V hr hd hk hV N policy
  markov := inferInstance
  conditional_law h := by
    change ((literalCycleLaw hn r d k V hr hd hk hV (returnedObservation N h).1 (policy h)).map
      (fun X => X::h)).map (returnedObservation N) = _
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    have he : (returnedObservation N ∘ fun X : CycleOutput n => X::h) = id := rfl
    rw [he, Measure.map_id]
  log_extend h := by
    change ∀ᵐ y ∂(literalCycleLaw hn r d k V hr hd hk hV (returnedObservation N h).1 (policy h)).map
      (fun X => X::h), y = returnedObservation N y :: h
    apply (ae_map_iff (measurable_of_countable _).aemeasurable
      (Set.to_countable {y : ReturnedHistory n | y = returnedObservation N y :: h}).measurableSet).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)

end
end RAF1519.Refinement
