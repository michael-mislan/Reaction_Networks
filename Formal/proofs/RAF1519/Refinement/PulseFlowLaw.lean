import proofs.RAF1519.Refinement.PulseFailureBudget
import proofs.RAF1519.Refinement.OperatingLaw
import Mathlib.Probability.Kernel.Composition.MeasureComp

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal
set_option maxHeartbeats 40000

abbrev MolecularPath (n : ℕ) := ℕ → JumpState (MolecularState n) (CountChannel n)

def molecularFlowKernel {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) : Kernel (MolecularState n) (MolecularPath n) :=
  ⟨molecularLaw hn r d k V hr hd hk hV,measurable_of_countable _⟩

instance molecularFlowKernel_markov {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) :
    IsMarkovKernel (molecularFlowKernel hn r d k V hr hd hk hV) :=
  ⟨fun N => molecularLaw_probability hn r d k V hr hd hk hV N⟩

def pulseFlowKernel {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    Kernel (PulseOutcomes N) (MolecularPath n) :=
  (molecularFlowKernel hn r d k V hr hd hk hV).comap (postPulseState N V p) (measurable_of_countable _)

instance pulseFlowKernel_markov {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    IsMarkovKernel (pulseFlowKernel hn r d k V hr hd hk hV N p) := by
  unfold pulseFlowKernel
  infer_instance

/-- Every pulse outcome starts its unrestricted physical flow from its actual counts. -/
def pulseFlowLaw {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    Measure (MolecularPath n) :=
  pulseFlowKernel hn r d k V hr hd hk hV N p ∘ₘ (graphPulsePMF N p).toMeasure

instance pulseFlowLaw_probability {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    IsProbabilityMeasure (pulseFlowLaw hn r d k V hr hd hk hV N p) := by
  unfold pulseFlowLaw
  infer_instance

end
end RAF1519.Refinement
