import proofs.EvolutionaryRescue.Source
import proofs.EvolutionaryRescue.Expansion
import proofs.EvolutionaryRescue.Barrier
import proofs.EvolutionaryRescue.Decision
import proofs.EvolutionaryRescue.ScalarBarrier
import proofs.EvolutionaryRescue.DecisionRegret

namespace EvolutionaryRescue

/-- Thin formal algebra root. The probability/ODE and enclosure proofs remain C/E. -/
theorem formal_components (i : Fin 6) :
    PersisterMemory.Source.meanAction (3/10) PersisterMemory.Source.extinctionWeight i ≤
      -(9/100)*PersisterMemory.Source.extinctionWeight i ∧
    (969581567445558/10^15:ℚ)-969579866104742/10^15 > 16/10^7 ∧
    (969623237350068/10^15:ℚ)-969621466763781/10^15 > 16/10^7 :=
  ⟨continuation_contracts i, displayed_interval_margins⟩

end EvolutionaryRescue
