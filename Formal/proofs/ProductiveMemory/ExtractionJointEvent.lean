import proofs.SerialTransferSelection.BatchEndpointGain
import proofs.ProductiveMemory.ExtractionNutrient
import proofs.ProductiveMemory.ExtractionOddsProbability
import proofs.ProductiveMemory.ExtractionQuota
import proofs.ProductiveMemory.ExtractionOutputProbability
import proofs.ProductiveMemory.ExtractionUnflagged
import proofs.ProductiveMemory.ExtractionAncestralPersistence
import proofs.ProductiveMemory.ExtractionChemicalProbability
import proofs.ProductiveMemory.ExtractionDeadlineProbability
import proofs.ResourceLimitedCompetition.ProbabilityUnion

namespace ProductiveMemory
set_option Elab.async false
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set
open scoped NNReal
noncomputable local instance ProductiveJointDecEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

def productiveBatchGoodSet (N W0 J H0 L0 : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | ∃ e, x=.inr e ∧ productiveReason N W0 J rho zL zH e=.nutrient ∧
    ValidVolumes N (productiveOutcome N e.1.val e.2).population ∧
    (∀ c ∈ (productiveOutcome N e.1.val e.2).population.live, extractionCellEnergy rho zL zH c < 8*readyLevel) ∧
    membrane (productiveOutcome N e.1.val e.2).population.live=4*W0 ∧
    H0 ≤ ancestralMembrane true (productiveOutcome N e.1.val e.2).population.live ∧
    L0 ≤ ancestralMembrane false (productiveOutcome N e.1.val e.2).population.live ∧
    (3/5)*Real.log 4-19/500 <
      Real.log (ancestralMembrane true (productiveOutcome N e.1.val e.2).population.live)-
      Real.log (ancestralMembrane false (productiveOutcome N e.1.val e.2).population.live)-(Real.log H0-Real.log L0) ∧
    5*W0 < (productiveOutcome N e.1.val e.2).collected ∧ (productiveOutcome N e.1.val e.2).collected < J}

def productiveBatchBadSets (N W0 J H0 L0 : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) : Fin 10 → Set (ProductiveStopped D) :=
  ![productiveOuterFailure N W0 J rho zL zH D, productiveDivisionFailure N W0 J rho zL zH D,
    productivePartitionFailureSet N W0 J rho zL zH D, productiveActiveSet D,
    productiveUnflaggedTerminalSet N W0 J rho zL zH D, productiveOddsExceptionalSet N H0 L0 D,
    productiveAncestryBelowSet N H0 true D, productiveAncestryBelowSet N L0 false D, productiveQuotaFailure N J D,productiveLowOutput N W0 D]

theorem productive_quota_reason (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState)
    (e : ProductivePopulationEvent D) (h : productiveReason N W0 J rho zL zH e=.collectionQuota) :
    J ≤ (productiveOutcome N e.1.val e.2).collected := by
  classical
  rcases e with ⟨s,e⟩
  cases e with
  | inl e => rcases e with ⟨i,r | d⟩ <;> simp only [productiveReason] at h <;> split_ifs at h
  | inr i =>
    change J ≤ s.val.collected+1
    simp only [productiveReason] at h
    split_ifs at h
    assumption

theorem productive_batch_bad_cover (N M W0 J H0 L0 : ℕ) (hN : 0 < N)
    (hH0 : 0 < H0) (hL0 : 0 < L0) (hw0 : H0+L0=W0) (rho zL zH : ℝ) :
    ∀ x ∈ (productiveBatchGoodSet N W0 J H0 L0 rho zL zH (productiveActiveDomain N M W0 J rho zL zH))ᶜ,
      ∃ i, x ∈ productiveBatchBadSets N W0 J H0 L0 rho zL zH (productiveActiveDomain N M W0 J rho zL zH) i := by
  classical
  intro x hx
  cases x with
  | inl s => exact ⟨3,s,rfl⟩
  | inr e =>
    by_cases hH : ancestralMembrane true (productiveOutcome N e.1.val e.2).population.live < H0
    · exact ⟨6,hH⟩
    by_cases hL : ancestralMembrane false (productiveOutcome N e.1.val e.2).population.live < L0
    · exact ⟨7,hL⟩
    by_cases ho : Sum.inr e ∈ productiveOddsExceptionalSet N H0 L0 (productiveActiveDomain N M W0 J rho zL zH)
    · exact ⟨5,ho⟩
    by_cases hquota : J ≤ (productiveOutcome N e.1.val e.2).collected
    · exact ⟨8,hquota⟩
    have heH := le_of_not_gt hH
    have heL := le_of_not_gt hL
    cases hr : productiveReason N W0 J rho zL zH e with
    | active => exact ⟨4,e,rfl,hr⟩
    | outer => exact ⟨0,e,rfl,hr⟩
    | divisionEnergy => exact ⟨1,e,rfl,hr⟩
    | partition => exact ⟨2,e,rfl,hr⟩
    | collectionQuota => exact ⟨8,productive_quota_reason N W0 J rho zL zH _ e hr⟩
    | nutrient =>
      by_cases hout : (productiveOutcome N e.1.val e.2).collected ≤ 5*W0
      · exact ⟨9,(productive_nutrient_resource N W0 J rho zL zH _ e.1 e.2 hr).2.1,hout⟩
      have hs := productive_active_safe N M W0 J rho zL zH e.1.val e.1.property
      have hv := productive_event_valid_volumes N hN e.1.val e.2 hs.2.2.2.2.1
      have he := productive_nutrient_energy N W0 J rho zL zH _ e.1 e.2 hs.2.2.2.2.2.1 hr
      have hw := productive_nutrient_membrane N M W0 J rho zL zH e.1 e.2 hr
      have htotal : ancestralMembrane true (productiveOutcome N e.1.val e.2).population.live+
          ancestralMembrane false (productiveOutcome N e.1.val e.2).population.live=4*(H0+L0) := by
        rw [ancestral_membrane_total,hw,hw0]
      have hg := SerialTransferSelection.phase_size_gain_of_nonexceptional N H0 L0 _ _ hN hH0 hL0
        (hH0.trans_le heH) (hL0.trans_le heL) htotal ho
      exact False.elim (hx ⟨e,rfl,hr,hv,he,hw,heH,heL,hg,lt_of_not_ge hout,lt_of_not_ge hquota⟩)

end ProductiveMemory
