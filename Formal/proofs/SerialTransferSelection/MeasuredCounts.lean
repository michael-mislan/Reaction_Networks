import proofs.SerialTransferSelection.NonvacuousInstance

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

noncomputable def chemicalCount (b : Bool) (cs : List TaggedCell) : ℕ :=
  (cs.filter (fun c => chemicalReadout c=b)).length

noncomputable def chemicalCountLogOdds (s : PopulationState) : ℝ :=
  Real.log (chemicalCount true s.live)-Real.log (chemicalCount false s.live)

theorem chemicalCount_eq_ancestralCount (b : Bool) (cs : List TaggedCell)
    (h : ∀ c ∈ cs, chemicalReadout c=c.high) : chemicalCount b cs=ancestralCount b cs := by
  unfold chemicalCount ancestralCount
  apply congrArg List.length
  apply List.filter_congr
  intro c hc
  rw [h c hc]

theorem chemicalCountLogOdds_eq (s : PopulationState)
    (h : ∀ c ∈ s.live, chemicalReadout c=c.high) : chemicalCountLogOdds s=countLogOdds s := by
  unfold chemicalCountLogOdds countLogOdds
  rw [chemicalCount_eq_ancestralCount true s.live h,chemicalCount_eq_ancestralCount false s.live h]

def measuredCountGain (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (y : ReadyPopulation N M zL zH) : Prop :=
  (∀ b, 0 < chemicalCount b y.val.live) ∧
    519/12250 < chemicalCountLogOdds y.val-chemicalCountLogOdds s

theorem realized_gain_is_measured (N M : ℕ) (zL zH : ℝ) (s : PopulationState)
    (hs : ∀ c ∈ s.live, chemicalReadout c=c.high) (y : ReadyPopulation N M zL zH)
    (hy : realizedCountGain N M zL zH s y) : measuredCountGain N M zL zH s y := by
  constructor
  · intro b
    rw [chemicalCount_eq_ancestralCount b y.val.live hy.2]
    exact hy.1.1 b
  · rw [chemicalCountLogOdds_eq y.val hy.2,chemicalCountLogOdds_eq s hs]
    exact hy.1.2

end SerialTransferSelection
