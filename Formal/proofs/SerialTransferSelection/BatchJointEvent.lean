import proofs.SerialTransferSelection.BatchEndpointGain
import proofs.SerialTransferSelection.BatchUnflaggedProbability
import proofs.SerialTransferSelection.BatchAncestralPersistence
import proofs.SerialTransferSelection.BatchChemicalProbability
import proofs.SerialTransferSelection.BatchDeadlineProbability
import proofs.ResourceLimitedCompetition.ProbabilityUnion

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance JointDecidableEq (D : Finset PopulationState) : DecidableEq (StoppedPopulation D) := Classical.decEq _

def phaseBatchGoodSet (N W0 H0 L0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) : Set (StoppedPopulation D) :=
  {x | ∃ e, x=.inr e ∧ phaseEventReason N W0 zL zH e=.nutrient ∧
    ValidVolumes N (eventOutcome N e) ∧
    (∀ c ∈ (eventOutcome N e).live, cellEnergy zL zH c < 8*innerEnergy) ∧
    membrane (eventOutcome N e).live=4*W0 ∧
    H0 ≤ ancestralMembrane true (eventOutcome N e).live ∧
    L0 ≤ ancestralMembrane false (eventOutcome N e).live ∧
    (3/5)*Real.log 4-19/500 <
      Real.log (ancestralMembrane true (eventOutcome N e).live)-
      Real.log (ancestralMembrane false (eventOutcome N e).live)-(Real.log H0-Real.log L0)}

def phaseBatchBadSets (N W0 H0 L0 : ℕ) (zL zH : ℝ) (D : Finset PopulationState) : Fin 8 → Set (StoppedPopulation D) :=
  ![phaseOuterFailureSet N W0 zL zH D, phaseDivisionFailureSet N W0 zL zH D,
    phasePartitionFailureSet N W0 zL zH D, activePopulationSet D,
    phaseUnflaggedTerminalSet N W0 zL zH D, oddsExceptionalSet N H0 L0 D,
    ancestryBelowSet N H0 true D, ancestryBelowSet N L0 false D]

theorem phase_batch_bad_cover (N M W0 H0 L0 : ℕ) (hN : 0 < N)
    (hH0 : 0 < H0) (hL0 : 0 < L0) (hw0 : H0+L0=W0) (zL zH : ℝ) :
    ∀ x ∈ (phaseBatchGoodSet N W0 H0 L0 zL zH (phaseActiveDomain N M W0 zL zH))ᶜ,
      ∃ i, x ∈ phaseBatchBadSets N W0 H0 L0 zL zH (phaseActiveDomain N M W0 zL zH) i := by
  classical
  intro x hx
  cases x with
  | inl s => exact ⟨3,s,rfl⟩
  | inr e =>
    by_cases hH : ancestralMembrane true (eventOutcome N e).live < H0
    · exact ⟨6,hH⟩
    by_cases hL : ancestralMembrane false (eventOutcome N e).live < L0
    · exact ⟨7,hL⟩
    by_cases ho : Sum.inr e ∈ oddsExceptionalSet N H0 L0 (phaseActiveDomain N M W0 zL zH)
    · exact ⟨5,ho⟩
    have heH := le_of_not_gt hH
    have heL := le_of_not_gt hL
    cases hr : phaseEventReason N W0 zL zH e with
    | active => exact ⟨4,e,rfl,hr⟩
    | outer => exact ⟨0,e,rfl,hr⟩
    | divisionEnergy => exact ⟨1,e,rfl,hr⟩
    | partition => exact ⟨2,e,rfl,hr⟩
    | nutrient =>
      have hs := phaseActiveDomain_safe N M W0 zL zH e.1.val e.1.property
      have hv := event_valid_volumes N hN _ e.1 e.2 hs.2.2.2.2.1
      have he := phase_nutrient_event_energy N W0 zL zH _ e.1 e.2 hs.2.2.2.2.2 hr
      have hw := phase_nutrient_endpoint_membrane N M W0 zL zH e.1 e.2 hr
      have htotal : ancestralMembrane true (eventOutcome N e).live+
          ancestralMembrane false (eventOutcome N e).live=4*(H0+L0) := by
        rw [ancestral_membrane_total,hw,hw0]
      have hg := phase_size_gain_of_nonexceptional N H0 L0 _ _ hN hH0 hL0
        (hH0.trans_le heH) (hL0.trans_le heL) htotal ho
      exact False.elim (hx ⟨e,rfl,hr,hv,he,hw,heH,heL,hg⟩)

end SerialTransferSelection
