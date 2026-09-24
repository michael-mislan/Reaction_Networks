import proofs.ResourceLimitedCompetition.MembraneConservation

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- The batch preparation depends only on total actual retained size. -/
def preparePhaseBatch (cells : List TaggedCell) : PopulationState :=
  ⟨4*membrane cells, cells, 0⟩

theorem preparePhaseBatch_conservation (cells : List TaggedCell) :
    (preparePhaseBatch cells).resource+membrane (preparePhaseBatch cells).live =
      5*membrane cells := by simp [preparePhaseBatch]; omega

theorem phase_batch_path_conservation (N : ℕ) (cells : List TaggedCell) (s : PopulationState)
    (hp : Relation.ReflTransGen (PopulationStep N) (preparePhaseBatch cells) s) :
    s.resource+membrane s.live=5*membrane cells :=
  (path_conservation hp).trans (preparePhaseBatch_conservation cells)

theorem phase_batch_endpoint (W0 : ℕ) (s : PopulationState)
    (hres : s.resource+membrane s.live=5*W0) (hQ : s.resource=W0) :
    membrane s.live=4*W0 := by omega

/-- Conservative bounds valid at all division phases, including terminal daughters. -/
theorem phase_batch_population_budget (N M W0 : ℕ) (hN : 0 < N)
    (hW : W0 ≤ 2*N*M) (s : PopulationState) (hv : ValidVolumes N s)
    (hres : s.resource+membrane s.live=5*W0) (hQ : W0 ≤ s.resource)
    (hlen : s.live.length=M+s.divisions) :
    s.live.length ≤ 8*M ∧ s.divisions ≤ 7*M := by
  have hlo := membrane_lower N s.live (fun c hc => (hv c hc).1)
  have hup : membrane s.live ≤ 4*W0 := by omega
  have hn : N*s.live.length ≤ N*(8*M) := by nlinarith only [hlo,hup,hW]
  have hc : s.live.length ≤ 8*M := by nlinarith only [hn,hN]
  omega

/-- A continuing state has strictly positive remaining division reserve. -/
theorem phase_batch_division_reserve (N M W0 : ℕ) (_hN : 0 < N)
    (hW : W0 ≤ 2*N*M) (s : PopulationState) (hv : ValidVolumes N s)
    (hres : s.resource+membrane s.live=5*W0) (hQ : W0 < s.resource)
    (hlen : s.live.length=M+s.divisions) : s.divisions < 7*M := by
  have hlo := membrane_lower N s.live (fun c hc => (hv c hc).1)
  have hup : membrane s.live < 4*W0 := by omega
  have hn : N*s.live.length < N*(8*M) := by nlinarith only [hlo,hup,hW]
  have hc : s.live.length < 8*M := by nlinarith only [hn,_hN]
  omega

/-- The old source's compound steps preserve the new preparation and budgets. -/
theorem phase_batch_path_budget (N : ℕ) (hN : 0 < N) (cells : List TaggedCell)
    (hv : ValidVolumes N (preparePhaseBatch cells)) (s : PopulationState)
    (hp : Relation.ReflTransGen (PopulationStep N) (preparePhaseBatch cells) s)
    (hQ : membrane cells ≤ s.resource) :
    s.resource+membrane s.live=5*membrane cells ∧
      s.live.length ≤ 8*cells.length ∧ s.divisions ≤ 7*cells.length := by
  have hs := path_valid_volumes hN hp hv
  have hc := phase_batch_path_conservation N cells s hp
  have hl := path_live_divisions hp (M := cells.length) (by simp [preparePhaseBatch])
  have hW : membrane cells ≤ 2*N*cells.length :=
    membrane_upper N cells (fun c hc => (hv c hc).2.le)
  exact ⟨hc, phase_batch_population_budget N cells.length (membrane cells) hN hW s hs hc hQ hl⟩

end SerialTransferSelection
