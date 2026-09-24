import proofs.RAF1519.Refinement.IntegerCycleLaw

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal BigOperators

abbrev CycleOutput (n : ℕ) := MolecularState n × (Fin n → Fin 5 → ℕ)

def cycleOutput {n : ℕ} (V : ℕ) (p : Fin n → Intervention) (z : MolecularPath n) : CycleOutput n :=
  ((z (countPathIndex z 4)).1, fun i => ![naturalMarkedWindow i .inventory z 3 4,
    naturalMarkedWindow i .freeX z 3 4,
    naturalMarkedWindow i .foodU z 0 4+pulseDose V (p i) 0,
    naturalMarkedWindow i .foodW z 0 4+pulseDose V (p i) 1,
    naturalMarkedWindow i .service z 0 4])

def cycleOutputSuccess {n : ℕ} (V : ℕ) (X : CycleOutput n) : Prop :=
  ∀ i, Ready (1/100) (concentration V (fun s => X.1 (i,s))) ∧
    ⌈(V:ℝ)/56⌉₊ ≤ X.2 i 0 ∧ ⌈(V:ℝ)/1080⌉₊ ≤ X.2 i 1 ∧
    X.2 i 2 ≤ 5*V ∧ X.2 i 3 ≤ 5*V ∧ X.2 i 4 ≤ ⌊(V:ℝ)/5⌋₊

theorem cycleOutput_measurable {n : ℕ} (V : ℕ) (p : Fin n → Intervention) :
    Measurable (cycleOutput V p) := by
  apply (molecularStateAt_measurable 4).prodMk
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  fin_cases j
  · exact naturalMarkedWindow_measurable i .inventory 3 4
  · exact naturalMarkedWindow_measurable i .freeX 3 4
  · exact (naturalMarkedWindow_measurable i .foodU 0 4).add_const _
  · exact (naturalMarkedWindow_measurable i .foodW 0 4).add_const _
  · exact naturalMarkedWindow_measurable i .service 0 4

theorem cycleOutput_success_iff {n : ℕ} (V : ℕ) (p : Fin n → Intervention) (z : MolecularPath n) :
    cycleOutputSuccess V (cycleOutput V p z) ↔ integerCycleSuccess V p z := Iff.rfl

def literalCycleLaw {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    Measure (CycleOutput n) :=
  (pulseFlowLaw hn r d k V hr hd hk hV N p).map (cycleOutput V p)

instance literalCycleLaw_probability {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    IsProbabilityMeasure (literalCycleLaw hn r d k V hr hd hk hV N p) :=
  Measure.isProbabilityMeasure_map (cycleOutput_measurable V p).aemeasurable

end
end RAF1519.Refinement
